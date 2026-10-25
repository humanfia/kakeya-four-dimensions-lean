import Submission.Obl.k4_scalar_angular_pair_agreement.PairTailBlock
import Submission.Obl.k4_scalar_angular_pair_agreement.BadPairs

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open Set MeasureTheory
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Original dyadic two-time pairs have either marginal dominated by twice the
original incidence law, after summing their unnormalized block weights. -/
theorem normalized_pair_tail_le {X : Type*} [MeasurableSpace X]
    (W T₁ : ℕ) (ν : Fin W → Measure X) (hν : ∀ w, SFinite (ν w))
    (ω : Fin W → ℝ) (Q : Fin W → Set (X × ℝ)) (hQ : ∀ w, MeasurableSet (Q w))
    (U : Fin W → Fin (2 ^ T₁) → Set (X × (ℝ × ℝ)))
    (hsub : ∀ w b z, z ∈ U w b → z.2.1 ∈ I T₁ b ∧ z.2.2 ∈ I T₁ b) :
    (∑ w : Fin W, ∑ b : Fin (2 ^ T₁), ENNReal.ofReal (ω w) * ENNReal.ofReal ((2 : ℝ) ^ T₁) *
      ((ν w).prod (volume.prod volume))
        (U w b ∩ {z | (z.1, z.2.1) ∈ Q w ∨ (z.1, z.2.2) ∈ Q w})) ≤
      2 * ∑ w : Fin W, ENNReal.ofReal (ω w) * ((ν w).prod volume) (Q w) := by
  have hscale : ENNReal.ofReal ((2 : ℝ) ^ T₁) *
      ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity)]
    norm_num
  calc
    _ ≤ ∑ w : Fin W, 2 * ENNReal.ofReal (ω w) * ((ν w).prod volume) (Q w) := by
      apply Finset.sum_le_sum
      intro w _
      let := hν w
      calc
        _ ≤ ∑ b : Fin (2 ^ T₁), ENNReal.ofReal (ω w) * ENNReal.ofReal ((2 : ℝ) ^ T₁) *
            (2 * ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹) *
              ((ν w).prod volume) (Q w ∩ univ ×ˢ I T₁ b)) := by
          apply Finset.sum_le_sum
          intro b _
          gcongr
          apply le_trans (measure_mono ?_) (pair_tail_block_le (ν w) (Q w) (hQ w) T₁ b)
          intro z hz
          exact ⟨(hsub w b z hz.1).1, (hsub w b z hz.1).2, hz.2⟩
        _ = 2 * ENNReal.ofReal (ω w) *
            ∑ b : Fin (2 ^ T₁), ((ν w).prod volume) (Q w ∩ univ ×ˢ I T₁ b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          calc
            _ = 2 * ENNReal.ofReal (ω w) *
                (ENNReal.ofReal ((2 : ℝ) ^ T₁) * ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹)) *
                ((ν w).prod volume) (Q w ∩ univ ×ˢ I T₁ b) := by ring
            _ = _ := by rw [hscale]; ring
        _ ≤ _ := by
          gcongr
          exact sum_coarse_le (ν w) ((ν w).prod volume) le_rfl (Q w) (hQ w) T₁
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _; ring

end Submission.Obl.k4_scalar_angular_pair_agreement
