/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/RegularizedPriorCore.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.DurationPriorCore

/-! Combine density and duration pruning while keeping a prescribed trace mask. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped ENNReal

/-- Starting from any common trace mask, make the incidence and its original restricted
prior comparable on one smaller mask.  The duration cap is measured on the old mask. -/
theorem exists_regularized_original_prior {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (ρ : Measure (X × ℝ))
    (K a ε : ℝ) (_hK : 0 ≤ K) (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hdom : ρ ≤ ENNReal.ofReal K • ν.prod volume)
    (E₀ : Set (X × ℝ)) (hE₀ : MeasurableSet E₀)
    (hunit : E₀ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (hloss₀ : ρ E₀ᶜ ≤ ENNReal.ofReal ε) :
    ∃ (θ : Measure X) (E : Set (X × ℝ)),
      θ ≤ ν ∧ θ Set.univ ≤ 1 ∧ MeasurableSet E ∧ E ⊆ E₀ ∧
      ρ Eᶜ ≤ ENNReal.ofReal (ε + 2 * a) ∧
      ENNReal.ofReal a • (θ.prod volume).restrict E ≤ ρ.restrict E ∧
      ρ.restrict E ≤ ENNReal.ofReal K • (θ.prod volume).restrict E ∧
      (∀ C : Set X, MeasurableSet C →
        ENNReal.ofReal a * θ C ≤ (ρ.restrict E₀) (C ×ˢ Set.univ)) := by
  have hS : MeasurableSet (Set.univ ×ˢ Set.Icc (0 : ℝ) 1 : Set (X × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hS₁ : ν.prod volume (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) ≤ 1 := by
    simp [Measure.prod_prod]
  obtain ⟨D, hD, hDsub, hDloss, hDlo, hDhi⟩ := exists_density_band_core
    (ν.prod volume) ρ (ENNReal.ofReal K) (ENNReal.ofReal a) ENNReal.ofReal_ne_top hdom
    (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) E₀ hS hS₁ hE₀ hunit
  obtain ⟨Λ, E, hΛ, hE, hEsub, hEΛ, hθν, hθ₁, hEloss, hprod, hduration⟩ :=
    exists_duration_prior_core ν ρ (ENNReal.ofReal K) (ENNReal.ofReal a)
      ENNReal.ofReal_ne_top hdom D hD
  have hprodE := hprod E Set.Subset.rfl
  have hloss : ρ Eᶜ ≤ ENNReal.ofReal (ε + 2 * a) := by
    calc
      _ ≤ ρ (E₀ᶜ ∪ ((E₀ \ D) ∪ (D \ E))) := by
        apply measure_mono
        intro p hp
        by_cases hp₀ : p ∈ E₀
        · by_cases hpD : p ∈ D
          · exact Or.inr (Or.inr ⟨hpD, hp⟩)
          · exact Or.inr (Or.inl ⟨hp₀, hpD⟩)
        · exact Or.inl hp₀
      _ ≤ ρ E₀ᶜ + (ρ (E₀ \ D) + ρ (D \ E)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ ENNReal.ofReal ε + (ENNReal.ofReal a + ENNReal.ofReal a) :=
        add_le_add hloss₀ (add_le_add hDloss hEloss)
      _ = ENNReal.ofReal (ε + 2 * a) := by
        rw [← ENNReal.ofReal_add ha ha, ← ENNReal.ofReal_add hε (add_nonneg ha ha)]
        congr 1
        ring
  have hlo := Measure.restrict_mono_measure hDlo E
  have hhi := Measure.restrict_mono_measure hDhi E
  rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset hEsub,
    Measure.restrict_restrict_of_subset hEsub, ← hprodE] at hlo
  rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset hEsub,
    Measure.restrict_restrict_of_subset hEsub, ← hprodE] at hhi
  refine ⟨ν.restrict Λ, E, hθν, hθ₁, hE, hEsub.trans hDsub, hloss, hlo, hhi, ?_⟩
  intro C hC
  exact (hduration C hC).trans
    ((Measure.restrict_mono_set ρ hDsub) (C ×ˢ Set.univ))

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
