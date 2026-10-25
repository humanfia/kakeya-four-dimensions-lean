/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameSourceNumerics.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

/-- Convert the lower block-count estimate to an upper length estimate. -/
theorem parent_length_upper {N K q s κ : ℝ} (hN : 0 < N) (hK : 0 < K)
    (hq : 0 < q) (hc : N ^ (κ * s) / K ≤ q⁻¹) :
    q ≤ K * N ^ (-κ * s) := by
  have hA : 0 < N ^ (κ * s) := Real.rpow_pos_of_pos hN _
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hK).mp hc) hq.le
  have hmul : q * N ^ (κ * s) ≤ K := by
    simpa only [mul_assoc, mul_left_comm q⁻¹ K, inv_mul_cancel₀ hq.ne', mul_one,
      mul_comm (N ^ (κ * s)) q] using hh
  calc
    q ≤ K / N ^ (κ * s) := (le_div_iff₀ hA).mpr hmul
    _ = K * N ^ (-κ * s) := by
      have he : -κ * s = -(κ * s) := by ring
      rw [he, Real.rpow_neg hN.le, div_eq_mul_inv]

/-- The loose late bound `K <= N` makes the parent length fixed-power large. -/
theorem parent_length_power_lower {N K q s κ : ℝ} (hN : 0 < N) (hq : 0 < q)
    (hKN : K ≤ N) (hc : q⁻¹ ≤ K * N ^ (κ * s)) :
    N ^ (-κ * s - 1) ≤ q := by
  have hh : q⁻¹ ≤ N ^ (κ * s + 1) := by
    calc
      q⁻¹ ≤ K * N ^ (κ * s) := hc
      _ ≤ N * N ^ (κ * s) := mul_le_mul_of_nonneg_right hKN (Real.rpow_nonneg hN.le _)
      _ = N ^ (κ * s + 1) := by rw [Real.rpow_add hN, Real.rpow_one, mul_comm]
  have hi := one_div_le_one_div_of_le (inv_pos.mpr hq) hh
  have he : -κ * s - 1 = -(κ * s + 1) := by ring
  simpa only [he, Real.rpow_neg hN.le, one_div, inv_inv] using hi

/-- A fixed parent depth has a fixed-power source floor. Only the loose
late bounds `K <= N` and `theta >= N^-1` are needed for this purpose. -/
theorem fixed_parent_mass_power_bound {N K θ q s d κ : ℝ}
    (hN : 2 ≤ N) (hK : 1 ≤ K) (hKN : K ≤ N) (hθ : N ^ (-1 : ℝ) ≤ θ)
    (hs : 0 ≤ s) (hd : d ≤ 1) (hκ : κ ≤ 1) (hq : N ^ (-κ * s - 1) ≤ q) :
    N ^ (-(5 * s + 7)) ≤ θ * (N ^ (-s)) ^ d * q ^ (4 : ℕ) / K ^ (2 : ℕ) := by
  have hN₀ : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hK₀ : 0 < K := by linarith
  have hθ₀ : 0 ≤ θ := (Real.rpow_nonneg hN₀.le _).trans hθ
  have ha : N ^ (-s) ≤ (N ^ (-s)) ^ d := by
    rw [← Real.rpow_mul hN₀.le]
    apply Real.rpow_le_rpow_of_exponent_le hN₁
    nlinarith [mul_le_mul_of_nonneg_right hd hs]
  have hq₄ : N ^ (-4 * κ * s - 4) ≤ q ^ (4 : ℕ) := by
    calc
      _ = (N ^ (-κ * s - 1)) ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN₀.le]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hN₀.le _) hq 4
  have hθa : N ^ (-1 : ℝ) * N ^ (-s) ≤ θ * (N ^ (-s)) ^ d :=
    mul_le_mul hθ ha (Real.rpow_nonneg hN₀.le _) hθ₀
  have hprod : N ^ (-1 : ℝ) * N ^ (-s) * N ^ (-4 * κ * s - 4) ≤
      θ * (N ^ (-s)) ^ d * q ^ (4 : ℕ) :=
    mul_le_mul hθa hq₄ (Real.rpow_nonneg hN₀.le _)
      (mul_nonneg hθ₀ (Real.rpow_nonneg (Real.rpow_nonneg hN₀.le _) _))
  apply (le_div_iff₀ (sq_pos_of_pos hK₀)).mpr
  calc
    _ ≤ N ^ (-(5 * s + 7)) * N ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK₀.le hKN 2) (Real.rpow_nonneg hN₀.le _)
    _ = N ^ (-5 * s - 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN₀]
      congr 1
      ring
    _ ≤ N ^ (-1 : ℝ) * N ^ (-s) * N ^ (-4 * κ * s - 4) := by
      rw [← Real.rpow_add hN₀, ← Real.rpow_add hN₀]
      apply Real.rpow_le_rpow_of_exponent_le hN₁
      nlinarith [mul_le_mul_of_nonneg_right hκ hs]
    _ ≤ _ := hprod

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
