/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/DurationPriorCore.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.DensityBandCore
import Submission.Lib.K4Homogenization.RetainedDuration

/-! A long-duration restriction of the original prior, compatible with every later mask. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped ENNReal

/-- Restricting the original prior to labels of sufficient retained duration costs only the
duration threshold.  On the retained event its product is exactly the original product. -/
theorem exists_duration_prior_core {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (ρ : Measure (X × ℝ))
    (U b : ℝ≥0∞) (hU : U ≠ ⊤) (hdom : ρ ≤ U • ν.prod volume)
    (E₀ : Set (X × ℝ)) (hE₀ : MeasurableSet E₀) :
    ∃ (Λ : Set X) (E : Set (X × ℝ)),
      MeasurableSet Λ ∧ MeasurableSet E ∧ E ⊆ E₀ ∧ E ⊆ Λ ×ˢ Set.univ ∧
      ν.restrict Λ ≤ ν ∧ (ν.restrict Λ) Set.univ ≤ 1 ∧
      ρ (E₀ \ E) ≤ b ∧
      (∀ D : Set (X × ℝ), D ⊆ E →
        ((ν.restrict Λ).prod volume).restrict D = (ν.prod volume).restrict D) ∧
      (∀ C : Set X, MeasurableSet C →
        b * (ν.restrict Λ) C ≤ (ρ.restrict E₀) (C ×ˢ Set.univ)) := by
  let G := ρ.rnDeriv (ν.prod volume)
  obtain ⟨hG, hρ, _⟩ :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw.exists_density_le hU hdom
  change Measurable G at hG
  change ρ = (ν.prod volume).withDensity G at hρ
  let G₀ := E₀.indicator G
  have hG₀ : Measurable G₀ := hG.indicator hE₀
  have hρ₀ : ρ.restrict E₀ = (ν.prod volume).withDensity G₀ := by
    rw [hρ, withDensity_indicator hE₀, restrict_withDensity hE₀]
  let Λ := Submission.Lib.K4Homogenization.durationRetained volume G₀ Set.univ b
  have hΛ : MeasurableSet Λ :=
    Submission.Lib.K4Homogenization.measurableSet_durationRetained volume hG₀ Set.univ b
  let E := E₀ ∩ (Λ ×ˢ Set.univ)
  have hE : MeasurableSet E := hE₀.inter (hΛ.prod MeasurableSet.univ)
  have hloss : ρ (E₀ \ E) ≤ b := by
    calc
      _ = (ρ.restrict E₀) (Λᶜ ×ˢ Set.univ) := by
        rw [Measure.restrict_apply (hΛ.compl.prod MeasurableSet.univ)]
        congr 1
        ext p
        simp only [E, mem_sdiff, mem_inter_iff, mem_prod, mem_compl_iff, mem_univ, and_true]
        tauto
      _ = (ν.prod volume).withDensity G₀ (Λᶜ ×ˢ Set.univ) := by rw [hρ₀]
      _ ≤ b * ν Set.univ :=
        Submission.Lib.K4Homogenization.duration_omission_mass_le ν volume hG₀
          MeasurableSet.univ b
      _ = b := by simp
  refine ⟨Λ, E, hΛ, hE, inter_subset_left, inter_subset_right,
    Measure.restrict_le_self, ?_, hloss, ?_, ?_⟩
  · simpa only [measure_univ] using (Measure.restrict_le_self (μ := ν) (s := Λ)) Set.univ
  · intro D hD
    rw [Measure.restrict_prod_eq_prod_univ,
      Measure.restrict_restrict_of_subset (hD.trans inter_subset_right)]
  · intro C hC
    have h := Submission.Lib.K4Homogenization.retained_duration_prior_cap ν volume hG₀
      MeasurableSet.univ b hC (C ×ˢ Set.univ) (by intro x hx t ht; exact ⟨hx, ht⟩)
    simpa only [hρ₀, Set.inter_univ, Set.univ_prod_univ, Measure.restrict_apply hC,
      Set.inter_comm] using h

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
