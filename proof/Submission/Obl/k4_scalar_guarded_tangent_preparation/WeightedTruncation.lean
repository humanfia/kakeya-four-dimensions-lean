import Submission.Obl.k4_scalar_guarded_tangent_preparation.UnnormalizedMeasured

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open Submission.Obl.k4_matching_cofinal_palette_selection

noncomputable section

/-- A weighted likelihood budget is spent on the original finite measures.
No world is rescaled after its likelihood mask is chosen. -/
theorem exists_weighted_original_truncation
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (σ : ι → Measure Ω) [∀ i, IsFiniteMeasure (σ i)]
    (ω : ι → ℝ) (hω : ∀ i, 0 ≤ ω i) (n : ι → ℕ)
    (X : ∀ i, Ω → Fin (n i)) (hX : ∀ i, Measurable (X i))
    (Y Z : ∀ i, Fin (n i) → ℕ) {R : ℝ} (hR : 1 < R)
    (hbudget : (∑ g, ω g * ∑ i, atomMass (σ g) (X g) i *
        max 0 (Real.log (originalLikelihood (atomMass (σ g) (X g)) (Y g) (Z g) i))) ≤
      ((∑ g, ω g * (σ g).real univ) / 2) * Real.log R) :
    ∃ (G : ι → Set Ω) (ρ : ι → Measure Ω),
      (∀ g, MeasurableSet (G g)) ∧
      (∀ g, ρ g = (σ g).restrict (G g)) ∧
      (∀ g, ρ g ≤ σ g) ∧
      ((∑ g, ω g * (σ g).real univ) / 2 ≤ ∑ g, ω g * (ρ g).real univ) ∧
      ∀ g (τ : Measure Ω), τ ≤ ρ g → ∀ e z : ℕ,
        τ.real {a | Y g (X g a) = e ∧ Z g (X g a) = z} * (σ g).real univ ≤
          R * (σ g).real {a | Y g (X g a) = e} *
            (σ g).real {a | Z g (X g a) = z} := by
  classical
  choose G hG hloss hcap using
    fun g => exists_unnormalized_measurable_truncation (σ g) (X g) (hX g) (Y g) (Z g) hR
  let ρ := fun g => (σ g).restrict (G g)
  refine ⟨G, ρ, hG, fun _ => rfl, fun _ => Measure.restrict_le_self, ?_, ?_⟩
  · have hlossWeighted : (∑ g, ω g * (σ g).real (G g)ᶜ) ≤
        (∑ g, ω g * (σ g).real univ) / 2 := by
      calc
        _ ≤ ∑ g, ω g * ((∑ i, atomMass (σ g) (X g) i *
            max 0 (Real.log (originalLikelihood (atomMass (σ g) (X g)) (Y g) (Z g) i))) /
              Real.log R) := Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hloss g) (hω g))
        _ = (∑ g, ω g * ∑ i, atomMass (σ g) (X g) i *
            max 0 (Real.log (originalLikelihood (atomMass (σ g) (X g)) (Y g) (Z g) i))) /
              Real.log R := by rw [Finset.sum_div]; simp_rw [mul_div_assoc]
        _ ≤ _ := (div_le_iff₀ (Real.log_pos hR)).2 hbudget
    have hsplit : (∑ g, ω g * (σ g).real univ) =
        (∑ g, ω g * (ρ g).real univ) + ∑ g, ω g * (σ g).real (G g)ᶜ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _
      have h := measureReal_add_measureReal_compl (μ := σ g) (hG g)
      have hrestrict : (ρ g).real univ = (σ g).real (G g) := by
        simp only [ρ, measureReal_def, Measure.restrict_apply_univ]
      rw [hrestrict, ← mul_add, h]
    linarith
  · intro g τ hτ e z
    exact hcap g τ hτ e z

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
