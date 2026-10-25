-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/ReturnMassNumerics.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Mathlib

namespace Submission.Obl.k4_finite_affine_candidate_return

/-- Exact tangent scaling and one multiplicative loss budget return the
native power floor. The dimension exponent is not rounded. -/
theorem native_floor_power_return
    (N Nt t d v loss A J : ℝ) (hN : 0 < N) (hNt : Nt = N ^ t) (hJ : 0 < J)
    (hallow : J * Nt ^ loss ≤ N ^ A) :
    N ^ (-(d * t * v) - A) ≤ J⁻¹ * Nt ^ (-d * v - loss) := by
  have hNt0 : 0 < Nt := by rw [hNt]; positivity
  have hpow : Nt ^ (-d * v) = N ^ (-(d * t * v)) := by
    rw [hNt, ← Real.rpow_mul hN.le]
    congr 1
    ring
  have hinv := inv_anti₀ (mul_pos hJ (Real.rpow_pos_of_pos hNt0 _)) hallow
  calc
    _ = N ^ (-(d * t * v)) * (N ^ A)⁻¹ := by rw [Real.rpow_sub hN]; ring
    _ ≤ N ^ (-(d * t * v)) * (J * Nt ^ loss)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = J⁻¹ * Nt ^ (-d * v - loss) := by
      rw [Real.rpow_sub hNt0, hpow]
      simp only [mul_inv_rev, div_eq_mul_inv]
      ring

/-- The exact old closed-block correspondence restores its time length,
and the source domination factor is the only mass loss. -/
theorem native_mass_coefficient_return
    (N Nt t d v loss A J q : ℝ) (hN : 0 < N) (hNt : Nt = N ^ t)
    (hJ : 0 < J) (hq : 0 < q) (Told Tnative : ℕ)
    (htime : q / (2 : ℝ) ^ Tnative = ((2 : ℝ) ^ Told)⁻¹)
    (hallow : J * Nt ^ loss ≤ N ^ A) :
    ENNReal.ofReal (N ^ (-(d * t * v) - A) / (2 : ℝ) ^ Told) ≤
      ENNReal.ofReal q * ((ENNReal.ofReal J)⁻¹ *
        ENNReal.ofReal (Nt ^ (-d * v - loss) / (2 : ℝ) ^ Tnative)) := by
  have hp := native_floor_power_return N Nt t d v loss A J hN hNt hJ hallow
  have hreal : N ^ (-(d * t * v) - A) / (2 : ℝ) ^ Told ≤
      (q / J) * (Nt ^ (-d * v - loss) / (2 : ℝ) ^ Tnative) := by
    apply (div_le_div_of_nonneg_right hp (by positivity)).trans_eq
    rw [div_eq_mul_inv, ← htime]
    ring
  apply (ENNReal.ofReal_le_ofReal hreal).trans_eq
  rw [ENNReal.ofReal_mul (div_nonneg hq.le hJ.le), ENNReal.ofReal_div_of_pos hJ,
    div_eq_mul_inv, mul_assoc]

/-- The separate full original H floor is strong enough to test an
auxiliary original strip at the fixed minimum gain. -/
theorem auxiliary_strip_coefficient_bound
    (N ρ h L ε J : ℝ) (T : ℕ) (hN : 1 ≤ N)
    (hρ : 0 ≤ ρ) (hh : 0 ≤ h) (hL : 0 ≤ L) (hε : 0 < ε) (hJ : 0 < J)
    (hJmax : J ≤ N ^ (ε / 1000000)) :
    ENNReal.ofReal (N ^ (-ρ * h * L - ε) / (2 : ℝ) ^ T) ≤
      ENNReal.ofReal ((((2 : ℝ) ^ T)⁻¹) / J) := by
  have hN0 : 0 < N := by linarith
  have hJbound : J ≤ N ^ (ρ * h * L + ε) := by
    apply hJmax.trans
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hprod : 0 ≤ ρ * h * L := by positivity
    linarith
  have hbase : N ^ (-ρ * h * L - ε) ≤ J⁻¹ := by
    calc
      _ = (N ^ (ρ * h * L + ε))⁻¹ := by
        rw [← Real.rpow_neg hN0.le]
        congr 1
        ring
      _ ≤ _ := inv_anti₀ hJ hJbound
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_of_nonneg_right hbase (by positivity)).trans_eq
  ring

end Submission.Obl.k4_finite_affine_candidate_return
