/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.Conditioning
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.CountedDensity

namespace Submission.Obl.k4_dyadic_crop_affine_laws.Framework

open MeasureTheory Set
open scoped ENNReal

/-- Restriction to the unit time interval makes a probability-prior incidence
law finite. -/
lemma finite_selected_incidence {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (E : Set (X × ℝ)) (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    IsFiniteMeasure ((ν.prod volume).restrict E) := by
  constructor
  calc
    ((ν.prod volume).restrict E) univ = (ν.prod volume) E := Measure.restrict_apply_univ E
    _ ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hE
    _ = 1 := by rw [Measure.prod_prod]; simp
    _ < ∞ := by simp

/-- Conditioning and an invertible change of trajectory coordinates commute
exactly with the selected incidence law. Time is unchanged. -/
theorem conditioned_selected_transport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [SFinite ν] (A : Set X) (E : Set (X × ℝ))
    (hA : MeasurableSet A) (hE : MeasurableSet E) (e : X ≃ᵐ Y) :
    (((conditionedPrior ν A e).prod volume).restrict
      ((e.prodCongr (MeasurableEquiv.refl ℝ)) '' (E ∩ (A ×ˢ univ)))) =
      (ν A)⁻¹ • (((ν.prod volume).restrict E).restrict (A ×ˢ univ)).map
        (e.prodCongr (MeasurableEquiv.refl ℝ)) := by
  let eT := e.prodCongr (MeasurableEquiv.refl ℝ)
  have hET : MeasurableSet (E ∩ (A ×ˢ (univ : Set ℝ))) := hE.inter (hA.prod MeasurableSet.univ)
  have hprod : ((ν.restrict A).map e).prod volume = ((ν.restrict A).prod volume).map eT := by
    change ((ν.restrict A).map e).prod volume =
      ((ν.restrict A).prod volume).map (Prod.map e id)
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (ν.restrict A) (volume : Measure ℝ) e.measurable
        (measurable_id : Measurable (id : ℝ → ℝ)))
  have hpr : (ν.restrict A).prod (volume : Measure ℝ) =
      (ν.prod volume).restrict (A ×ˢ univ) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) A univ)
  rw [conditionedPrior, Measure.prod_smul_left, Measure.restrict_smul, hprod]
  congr 1
  rw [Measure.restrict_map eT.measurable (eT.measurableSet_image.mpr hET)]
  rw [Set.preimage_image_eq _ eT.injective, hpr,
    Measure.restrict_restrict hET, Measure.restrict_restrict (hA.prod MeasurableSet.univ)]
  congr 2
  ext p
  simp only [mem_inter_iff, mem_prod, mem_univ, and_true]
  tauto

/-- Absolute continuity of a counted observation implies absolute continuity of
its continuous marginal. -/
lemma absolutelyContinuous_fst_of_prod_count {X B : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Countable B] [MeasurableSingletonClass B]
    (ξ : Measure (X × B)) (ν : Measure X) (h : ξ ≪ ν.prod Measure.count) :
    ξ.map Prod.fst ≪ ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hnull
  rw [Measure.map_apply measurable_fst hS]
  apply h
  rw [show Prod.fst ⁻¹' S = S ×ˢ (univ : Set B) by ext p; simp]
  rw [Measure.prod_prod, hnull, zero_mul]

/-- Two countable labels may be discarded from an absolutely continuous joint
law, leaving an absolutely continuous continuous-base marginal. -/
lemma base_marginal_ac_of_joint {A X B C : Type*}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace B] [MeasurableSpace C]
    [Countable B] [MeasurableSingletonClass B] [Countable C] [MeasurableSingletonClass C]
    (μ : Measure A) (ξ : Measure X) (f : A → (X × B) × C) (hf : Measurable f)
    (h : μ.map f ≪ (ξ.prod Measure.count).prod Measure.count) :
    μ.map (fun p => (f p).1.1) ≪ ξ := by
  have h₁ := absolutelyContinuous_fst_of_prod_count (μ.map f) (ξ.prod Measure.count) h
  have h₂ := absolutelyContinuous_fst_of_prod_count ((μ.map f).map Prod.fst) ξ h₁
  rw [Measure.map_map measurable_fst hf,
    Measure.map_map measurable_fst (measurable_fst.comp hf)] at h₂
  exact h₂

/-- Cropping preserves absolute continuity of the continuous observation law.
Only the commuting observation maps and preservation of base null sets are used. -/
lemma conditioned_base_absolutelyContinuous {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure X) [SFinite ν] (A : Set X) (E : Set (X × ℝ))
    (hA : MeasurableSet A) (hE : MeasurableSet E) (e : X ≃ᵐ Y)
    (b : X × ℝ → Z) (b' : Y × ℝ → Z) (hb : Measurable b) (hb' : Measurable b')
    (h : Z ≃ᵐ Z) (hcomm : ∀ p, b' ((e.prodCongr (MeasurableEquiv.refl ℝ)) p) = h (b p))
    (ξ : Measure Z) (hbase : ((ν.prod volume).restrict E).map b ≪ ξ)
    (hJac : ξ.map h ≪ ξ) :
    ((((conditionedPrior ν A e).prod volume).restrict
      ((e.prodCongr (MeasurableEquiv.refl ℝ)) '' (E ∩ (A ×ˢ univ)))).map b') ≪ ξ := by
  have hrest : (((ν.prod (volume : Measure ℝ)).restrict E).restrict (A ×ˢ univ)).map b ≪ ξ :=
    ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).map hb).trans hbase
  have hmaps := (hrest.map h.measurable).trans hJac
  rw [conditioned_selected_transport ν A E hA hE e,
    Measure.map_smul _ hb'.aemeasurable,
    Measure.map_map hb' (e.prodCongr (MeasurableEquiv.refl ℝ)).measurable,
    show b' ∘ (e.prodCongr (MeasurableEquiv.refl ℝ)) = h ∘ b by funext p; exact hcomm p,
    ← Measure.map_map h.measurable hb]
  exact Measure.smul_absolutelyContinuous.trans hmaps

end Submission.Obl.k4_dyadic_crop_affine_laws.Framework
