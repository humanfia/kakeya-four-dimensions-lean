import Mathlib

namespace Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

/-- The same original mass pays for the state and trajectory losses. The
state table's volume is measured in the original contact units. -/
theorem pruning_reference_losses {N K H a b ω d v η δ W m : ℝ} {n : ℕ}
    (hN : 0 < N) (hK : 1 ≤ K) (hH : 0 < H) (ha : 0 < a) (hb : 0 < b)
    (hω : 0 < ω) (hm : 0 ≤ m)
    (hscale : b ^ d * N ^ (d * v) = a ^ d)
    (hcount : (n : ℝ) * ω ^ 3 ≤ 1073741824 * K ^ 20 * N ^ (d * v))
    (hWrel : N ^ (-η) * H * m ≤ W)
    (hWabs : N ^ (-η) * H ^ 4 * a ^ d / K ^ 2 ≤ W)
    (hstate : 4294967296 * K ^ 22 * N ^ (-(δ / 4)) ≤ N ^ (-η))
    (hline : 4 * N ^ (-(δ / 4)) ≤ N ^ (-η))
    (htransport : 2 * N ^ (-δ) ≤ N ^ (-η)) :
    4 * ((n : ℝ) * (H ^ 4 * ω ^ 3 * b ^ d) * N ^ (-(δ / 4))) ≤ W ∧
      4 * (N ^ (-(δ / 4)) * H * m) ≤ W ∧
      2 * (N ^ (-δ) * H * m) ≤ W := by
  have hK0 : 0 < K := by linarith
  have href : 0 ≤ H ^ 4 * b ^ d * N ^ (-(δ / 4)) := by positivity
  have hsum : (n : ℝ) * (H ^ 4 * ω ^ 3 * b ^ d) * N ^ (-(δ / 4)) ≤
      1073741824 * K ^ 20 * N ^ (-(δ / 4)) * H ^ 4 * a ^ d := by
    calc
      _ = ((n : ℝ) * ω ^ 3) * (H ^ 4 * b ^ d * N ^ (-(δ / 4))) := by ring
      _ ≤ (1073741824 * K ^ 20 * N ^ (d * v)) *
          (H ^ 4 * b ^ d * N ^ (-(δ / 4))) := mul_le_mul_of_nonneg_right hcount href
      _ = 1073741824 * K ^ 20 * N ^ (-(δ / 4)) * H ^ 4 *
          (b ^ d * N ^ (d * v)) := by ring
      _ = _ := by rw [hscale]
  refine ⟨?_, ?_, ?_⟩
  · apply le_trans _ hWabs
    apply (le_div_iff₀ (sq_pos_of_pos hK0)).mpr
    calc
      _ ≤ (4 * (1073741824 * K ^ 20 * N ^ (-(δ / 4)) * H ^ 4 * a ^ d)) * K ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num))
          (sq_nonneg K)
      _ = (4294967296 * K ^ 22 * N ^ (-(δ / 4))) * (H ^ 4 * a ^ d) := by ring
      _ ≤ N ^ (-η) * (H ^ 4 * a ^ d) := mul_le_mul_of_nonneg_right hstate (by positivity)
      _ = _ := by ring
  · apply le_trans _ hWrel
    nlinarith only [mul_le_mul_of_nonneg_right hline (mul_nonneg hH.le hm)]
  · apply le_trans _ hWrel
    nlinarith only [mul_le_mul_of_nonneg_right htransport (mul_nonneg hH.le hm)]

/-- Half the original primitive mass remains after the two simultaneous
reference losses, and every original intercept-bin transport floor is paid. -/
theorem surviving_mass_of_reference_losses {W M B C T : ℝ}
    (hW : 0 < W) (hB : 4 * B ≤ W) (hC : 4 * C ≤ W)
    (hT : 2 * T ≤ W) (hmass : W ≤ M + (B + C)) :
    0 < M ∧ W / 2 ≤ M ∧ T ≤ M := by
  constructor
  · linarith
  · constructor <;> linarith

end

end Submission.Obl.k4_critical_switching_state_preparation
