import Submission.Obl.k4_pair_bin_atlas_assembly.PairData
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftBounds

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Filter

/-- A fixed degree envelope absorbs the affine substitution coefficients. -/
theorem physical_coefficient_budget {N : ℝ} (hN : 2 ≤ N) (M K : ℕ) :
    81 * N ^ M * (6 * (N ^ K) ^ 2) ^ 2 ≤ N ^ (M + 4 * K + 12) := by
  calc
    _ = 2916 * N ^ (M + 4 * K) := by
      simp only [pow_add, pow_mul]
      ring
    _ ≤ N ^ (M + 4 * K + 12) :=
      Submission.Obl.k4_native_finite_terminal_atlas_lift.power_absorbs_constant
        hN (M + 4 * K) 12 (by norm_num)

/-- Source unions, incidence restrictions and polynomial tests fit in a
uniform power budget, before the output slack is specified. -/
theorem chart_format_budget {N m : ℝ} (hN : 2 ≤ N) (M Me : ℕ)
    (hm : m ≤ N ^ M) :
    N ^ Me + (((m * N ^ M + 14) + (2 + m * N ^ M))) ≤
      N ^ (2 * M + Me + 5) := by
  have hN1 : 1 ≤ N := by linarith
  have hX : 1 ≤ N ^ M := one_le_pow₀ hN1
  have hY : 1 ≤ N ^ Me := one_le_pow₀ hN1
  have hX0 : 0 ≤ N ^ M := by positivity
  have hXX : m * N ^ M ≤ (N ^ M) ^ 2 := by nlinarith
  have hsq : 1 ≤ (N ^ M) ^ 2 := by nlinarith
  have hXY : (N ^ M) ^ 2 ≤ (N ^ M) ^ 2 * N ^ Me := by nlinarith
  have hYX : N ^ Me ≤ (N ^ M) ^ 2 * N ^ Me := by nlinarith
  have hprod : 1 ≤ (N ^ M) ^ 2 * N ^ Me := by nlinarith
  calc
    _ ≤ 19 * ((N ^ M) ^ 2 * N ^ Me) := by nlinarith
    _ = 19 * N ^ (2 * M + Me) := by
      rw [pow_add, mul_comm 2 M, pow_mul]
    _ ≤ N ^ (2 * M + Me + 5) :=
      Submission.Obl.k4_native_finite_terminal_atlas_lift.power_absorbs_constant
        hN (2 * M + Me) 5 (by norm_num)

end Submission.Obl.k4_pair_bin_atlas_assembly
