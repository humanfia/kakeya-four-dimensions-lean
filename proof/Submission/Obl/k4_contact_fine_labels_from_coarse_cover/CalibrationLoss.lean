-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/CalibrationLoss.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelBounds

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Filter

/-- The explicit loss in original mesh calibration is polynomial in the
original subpower budget, even when its universal exponent is real. -/
theorem calibration_loss_polynomial {C : ℝ} (hC : 1 ≤ C) :
    ∃ (A : ℝ) (n : ℕ), 0 ≤ A ∧ ∀ K : ℝ, 1 ≤ K →
      C * (1 + 2 * K) ^ C *
        (1 + ((2 * K + 5) * K) / K⁻¹) ^ (6 : ℕ) ≤ A * K ^ n := by
  let M : ℕ := ⌈C⌉₊
  refine ⟨C * 3 ^ M * 8 ^ (6 : ℕ), M + 18, by positivity, ?_⟩
  intro K hK
  have hK0 : 0 < K := by linarith
  have hCM : C ≤ (M : ℝ) := Nat.le_ceil _
  have hfirst : (1 + 2 * K) ^ C ≤ (3 * K) ^ M := by
    calc
      _ ≤ (1 + 2 * K) ^ (M : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hCM
      _ = (1 + 2 * K) ^ M := Real.rpow_natCast _ _
      _ ≤ (3 * K) ^ M := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have hsmall : 1 + ((2 * K + 5) * K) / K⁻¹ ≤ 8 * K ^ 3 := by
    have heq : ((2 * K + 5) * K) / K⁻¹ = (2 * K + 5) * K ^ 2 := by
      field_simp
    rw [heq]
    have hmult := mul_le_mul_of_nonneg_right (show 2 * K + 5 ≤ 7 * K by linarith)
      (sq_nonneg K)
    nlinarith
  calc
    _ ≤ C * (3 * K) ^ M * (8 * K ^ 3) ^ (6 : ℕ) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hfirst (by linarith)
      · exact pow_le_pow_left₀ (by positivity) hsmall _
      · positivity
      · positivity
    _ = (C * 3 ^ M * 8 ^ (6 : ℕ)) * K ^ (M + 18) := by
      simp only [mul_pow, ← pow_mul, pow_add]
      ring

namespace Model

variable {α : Type*} [MeasurableSpace α] (p : Model α)

theorem eventually_calibration_loss_le (hp : p.Valid) {C ε : ℝ}
    (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ k in atTop, C * (1 + 2 * p.K k) ^ C *
      (1 + ((2 * p.K k + 5) * p.K k) / (p.K k)⁻¹) ^ (6 : ℕ) ≤ p.N k ^ ε := by
  obtain ⟨A, n, hA, hbound⟩ := calibration_loss_polynomial hC
  have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => (hp.N_ge k).trans' (by norm_num : (1 : ℝ) ≤ 2))
    hp.N_lim hp.K_ge hp.K_sub n (show (0 : ℝ) < ε from hε) hA
  filter_upwards [h] with k hk
  exact (hbound (p.K k) (hp.K_ge k)).trans (by simpa only [Real.rpow_zero, mul_one] using hk.le)

end Model

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
