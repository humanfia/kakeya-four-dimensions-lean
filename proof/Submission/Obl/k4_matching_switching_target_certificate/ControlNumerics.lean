import Mathlib

namespace Submission.Obl.k4_matching_switching_target_certificate

/-- The fixed grid margins absorb the palette and derivative prediction errors. -/
theorem control_errors_small {q : ℕ} (hq : 1 ≤ q) {N ε γ : ℝ}
    (hN : 1 ≤ N) (hε : 0 ≤ ε) (hεq : ε ≤ 1 / (q : ℝ))
    (hγ : 4 / (q : ℝ) ≤ γ) (hroot : 32 ≤ N ^ (1 / (q : ℝ))) :
    N ^ (-(6 / (q : ℝ))) + (3 + N ^ ε) * N ^ (-γ) ≤ N ^ (-(2 / (q : ℝ))) ∧
    2 * N ^ (-(6 / (q : ℝ))) + (6 + 8 * N ^ ε) * N ^ (-γ) ≤ N ^ (-ε) / 2 := by
  have hN0 : 0 < N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hNe : 1 ≤ N ^ ε := Real.one_le_rpow hN hε
  have h6 : N ^ (-(6 / (q : ℝ))) ≤ N ^ (-(3 / (q : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg
      (div_le_div_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 6) (Nat.cast_nonneg q)))
  have hprod : N ^ ε * N ^ (-γ) ≤ N ^ (-(3 / (q : ℝ))) := by
    rw [← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN
    simp only [div_eq_mul_inv, one_mul] at hεq hγ ⊢
    linarith
  have hE : N ^ (-(6 / (q : ℝ))) + (3 + N ^ ε) * N ^ (-γ) ≤
      5 * N ^ (-(3 / (q : ℝ))) := by
    have hcoef : (3 + N ^ ε) * N ^ (-γ) ≤ 4 * (N ^ ε * N ^ (-γ)) := by
      have hpos : 0 ≤ N ^ (-γ) := by positivity
      nlinarith
    linarith
  have hsep : 2 * N ^ (-(6 / (q : ℝ))) + (6 + 8 * N ^ ε) * N ^ (-γ) ≤
      16 * N ^ (-(3 / (q : ℝ))) := by
    have hcoef : (6 + 8 * N ^ ε) * N ^ (-γ) ≤ 14 * (N ^ ε * N ^ (-γ)) := by
      have hpos : 0 ≤ N ^ (-γ) := by positivity
      nlinarith
    linarith
  have h32 : 32 * N ^ (-(3 / (q : ℝ))) ≤ N ^ (-(2 / (q : ℝ))) := by
    calc 32 * N ^ (-(3 / (q : ℝ))) ≤ N ^ (1 / (q : ℝ)) * N ^ (-(3 / (q : ℝ))) := by
          gcongr
      _ = N ^ (-(2 / (q : ℝ))) := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hlast : N ^ (-(2 / (q : ℝ))) ≤ N ^ (-ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hN
    have : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
    simp only [div_eq_mul_inv, one_mul] at hεq this ⊢
    linarith
  constructor
  · refine hE.trans ?_
    have hp : 0 ≤ N ^ (-(3 / (q : ℝ))) := by positivity
    linarith
  · linarith

lemma root_large_of_scale {q : ℕ} (hq : 1 ≤ q) {N : ℝ} (hN : (32 : ℝ) ^ q ≤ N) :
    32 ≤ N ^ (1 / (q : ℝ)) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hpow : ((32 : ℝ) ^ q) ^ (1 / (q : ℝ)) = 32 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 32)]
    rw [mul_one_div_cancel hq0, Real.rpow_one]
  rw [← hpow]
  exact Real.rpow_le_rpow (by positivity) hN (by positivity)

end Submission.Obl.k4_matching_switching_target_certificate
