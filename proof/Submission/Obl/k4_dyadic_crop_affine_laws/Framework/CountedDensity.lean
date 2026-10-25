/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

/-
Adapted from this LOT tree, obligation o006, session x0006, branch x0006,
Submission/Obl/k4_core/Framework/CountedDensity.lean.
Original code and any earlier attribution are retained below.
-/

import Mathlib

/-!
# Adding countable observation labels to a density

Absolute continuity of the continuous base marginal supplies a joint density after
adjoining arbitrary measurable countable labels. This applies successively to the
hidden bin and the two-dimensional angular bin in the exact-problem interface.
-/

namespace Submission.Obl.k4_dyadic_crop_affine_laws.Framework

open Set MeasureTheory

/-- A measure with an absolutely continuous first marginal remains absolutely
continuous after adjoining a countable label, against counting measure. -/
theorem absolutelyContinuous_prod_count_of_fst {X B : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Countable B] [MeasurableSingletonClass B]
    (ξ : Measure (X × B)) (ν : Measure X) (h : ξ.map Prod.fst ≪ ν) :
    ξ ≪ ν.prod Measure.count := by
  classical
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hnull
  let A : Set X := {x | ∃ b : B, (x, b) ∈ S}
  have hA : MeasurableSet A := by
    have heq : A = ⋃ b : B, (fun x : X => (x, b)) ⁻¹' S := by
      ext x
      simp [A]
    rw [heq]
    exact MeasurableSet.iUnion fun b => hS.preimage (measurable_id.prodMk measurable_const)
  have hsections := (Measure.measure_prod_null hS).mp hnull
  have hnot : ∀ᵐ x ∂ν, x ∉ A := by
    filter_upwards [hsections] with x hx
    rintro ⟨b, hb⟩
    have hempty := Measure.count_eq_zero_iff.mp hx
    have : b ∈ Prod.mk x ⁻¹' S := hb
    simp only [hempty, Set.mem_empty_iff_false] at this
  have hA₀ : ν A = 0 := by
    simpa [ae_iff] using hnot
  have hmap : ξ (Prod.fst ⁻¹' A) = 0 := by
    simpa only [Measure.map_apply measurable_fst hA] using h hA₀
  apply measure_mono_null (t := Prod.fst ⁻¹' A) ?_ hmap
  rintro ⟨x, b⟩ hx
  exact ⟨b, hx⟩

/-- A finite observation law admits a measurable density against base volume times
counting measure whenever its continuous base marginal is absolutely continuous. -/
theorem exists_counted_observation_density {A X B : Type*}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B]
    (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f : A → X × B) (hf : Measurable f)
    (hbase : μ.map (fun a => (f a).1) ≪ ν) :
    ∃ ρ : X × B → ENNReal, Measurable ρ ∧ μ.map f = (ν.prod Measure.count).withDensity ρ := by
  have hfst : (μ.map f).map Prod.fst ≪ ν := by
    simpa only [Measure.map_map measurable_fst hf, Function.comp_def] using hbase
  have hfull := absolutelyContinuous_prod_count_of_fst (μ.map f) ν hfst
  exact ⟨(μ.map f).rnDeriv (ν.prod Measure.count), Measure.measurable_rnDeriv _ _,
    (Measure.withDensity_rnDeriv_eq _ _ hfull).symm⟩

/-- A finite absolutely continuous law supported on a measurable set admits a
measurable density that vanishes pointwise outside that set. -/
theorem exists_density_with_support {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [SigmaFinite ν] (hac : μ ≪ ν)
    (R : Set X) (hR : MeasurableSet R) (hsupport : ∀ᵐ x ∂μ, x ∈ R) :
    ∃ ρ : X → ENNReal, Measurable ρ ∧ μ = ν.withDensity ρ ∧ ∀ x ∉ R, ρ x = 0 := by
  classical
  let ρ := μ.rnDeriv ν
  have hρ : Measurable ρ := Measure.measurable_rnDeriv _ _
  have hRN : ν.withDensity ρ = μ := Measure.withDensity_rnDeriv_eq _ _ hac
  refine ⟨R.indicator ρ, hρ.indicator hR, ?_, ?_⟩
  · calc
      μ = μ.restrict R := (Measure.restrict_eq_self_of_ae_mem hsupport).symm
      _ = (ν.withDensity ρ).restrict R := by rw [hRN]
      _ = ν.withDensity (R.indicator ρ) := by
        rw [restrict_withDensity hR, withDensity_indicator hR]
  · intro x hx
    exact Set.indicator_of_notMem hx ρ

/-- Countably labeled observations have a density with any measurable geometric
support relation respected pointwise by its chosen representative. -/
theorem exists_counted_observation_density_with_support {A X B : Type*}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B]
    (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f : A → X × B) (hf : Measurable f)
    (hbase : μ.map (fun a => (f a).1) ≪ ν)
    (R : Set (X × B)) (hR : MeasurableSet R) (hsupport : ∀ᵐ a ∂μ, f a ∈ R) :
    ∃ ρ : X × B → ENNReal, Measurable ρ ∧
      μ.map f = (ν.prod Measure.count).withDensity ρ ∧ ∀ x ∉ R, ρ x = 0 := by
  have hfst : (μ.map f).map Prod.fst ≪ ν := by
    simpa only [Measure.map_map measurable_fst hf, Function.comp_def] using hbase
  have hfull := absolutelyContinuous_prod_count_of_fst (μ.map f) ν hfst
  apply exists_density_with_support (μ.map f) (ν.prod Measure.count) hfull R hR
  exact (ae_map_iff hf.aemeasurable hR).mpr hsupport

end Submission.Obl.k4_dyadic_crop_affine_laws.Framework
