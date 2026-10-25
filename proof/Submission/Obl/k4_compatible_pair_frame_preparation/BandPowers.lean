-- Adapted from this LOT tree, o114, session x0680, branch x0680,
-- Submission/Obl/k4_terminal_representative_atlas/Preparation/BandPowers.lean.

import Submission.Obl.k4_compatible_pair_frame_preparation.BandProfile

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Band

/-- The profile interpolation has a fixed power cost at the common density
scale. The geometric determinant budget is the sole input in `hJ`. -/
theorem band_coefficient_power_budget {N K J σ fL τ d u e b : ℝ}
    (hN : 1 < N) (hK0 : 0 ≤ K)
    (hσ0 : 0 ≤ σ) (hd : d ≤ 1) (hlarge : 64 ≤ N ^ e)
    (hK : K ≤ N ^ e) (hτ : τ ≤ e) (hmesh : d * u ≤ e)
    (hJ : N ^ (-fL) * J ≤ σ * N ^ b) :
    (32 * K ^ 2 * N ^ (-fL + τ) * J) * (2 : ℝ) ^ d * N ^ (d * u) ≤
      σ * N ^ (b + 5 * e) := by
  have hN0 : 0 < N := by linarith
  have htwo : (2 : ℝ) ^ d ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hd
  have hconst : 32 * (2 : ℝ) ^ d ≤ N ^ e := by linarith
  have hKsq : K ^ 2 ≤ (N ^ e) ^ (2 : ℕ) := by gcongr
  calc
    _ = (N ^ (-fL) * J) * (32 * (2 : ℝ) ^ d) * K ^ 2 * N ^ τ * N ^ (d * u) := by
      rw [Real.rpow_add hN0]
      ring
    _ ≤ (σ * N ^ b) * N ^ e * (N ^ e) ^ (2 : ℕ) * N ^ e * N ^ e := by
      gcongr <;> exact hN.le
    _ = σ * N ^ (b + 5 * e) := by
      rw [← Real.rpow_mul_natCast hN0.le e 2]
      repeat rw [mul_assoc]
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0,
        ← Real.rpow_add hN0]
      congr 2
      ring

end Submission.Obl.k4_compatible_pair_frame_preparation.Band
