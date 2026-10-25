import Mathlib

/-!
# Basic asymptotic helpers

Powers of a large base: monotonicity in the exponent, products, and "a constant times a
negative power is at most one for large bases".
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

noncomputable section

theorem rpow_le_rpow_exp {N a b : ℝ} (hN : 1 ≤ N) (hab : a ≤ b) : N ^ a ≤ N ^ b :=
  Real.rpow_le_rpow_of_exponent_le hN hab

theorem rpow_mul_rpow {N a b : ℝ} (hN : 0 < N) : N ^ a * N ^ b = N ^ (a + b) :=
  (Real.rpow_add hN a b).symm

/-- A constant times a negative power is small for large bases. -/
theorem const_mul_rpow_le_one {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → C * N ^ (-δ) ≤ 1 := by
  refine ⟨max 1 (C ^ (1 / δ)), le_max_left _ _, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hCN : C ^ (1 / δ) ≤ N := (le_max_right _ _).trans hN
  have hC' : C ≤ N ^ δ := by
    calc C = (C ^ (1 / δ)) ^ δ := by
          rw [← Real.rpow_mul hC, one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
      _ ≤ N ^ δ := Real.rpow_le_rpow (Real.rpow_nonneg hC _) hCN hδ.le
  rw [Real.rpow_neg hN0.le]
  calc C * (N ^ δ)⁻¹ ≤ N ^ δ * (N ^ δ)⁻¹ :=
        mul_le_mul_of_nonneg_right hC' (inv_nonneg.mpr (Real.rpow_nonneg hN0.le _))
    _ = 1 := mul_inv_cancel₀ (Real.rpow_pos_of_pos hN0 _).ne'

/-- Powers of a quantity bounded by a power. -/
theorem pow_le_rpow_mul {K N η : ℝ} (hK : 1 ≤ K) (hKη : K ≤ N ^ η) (hN : 0 < N) (n : ℕ) :
    K ^ n ≤ N ^ ((n : ℝ) * η) := by
  rw [mul_comm, Real.rpow_mul_natCast hN.le]
  exact pow_le_pow_left₀ (by linarith) hKη n

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
