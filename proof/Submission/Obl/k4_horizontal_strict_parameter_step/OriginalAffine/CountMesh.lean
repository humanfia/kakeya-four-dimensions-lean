import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Submission.Obl.k4_horizontal_strict_parameter_step

/-- A mesh resolving the quadratic transverse side also resolves the common
reference contact box. Only the reference position and velocity enter. -/
theorem count_mesh_of_square_floor {K q η p v m : ℝ}
    (hK : 1 ≤ K) (hq : 0 ≤ q) (hη : 0 ≤ η)
    (hηq : η ≤ q / 2) (hηq₂ : η ≤ q ^ 2)
    (hp : |p| ≤ 3 * K) (hv : |v| ≤ K ^ 2) (hm : |m| ≤ 1) :
    (|v| + 1) * η ≤ 8 * K ^ 2 * q ∧
      (|-p - m * v| + |m| + 1) * η ≤ 32 * K ^ 4 * q ^ 2 := by
  have hK₀ : 0 ≤ K := by linarith
  have hK₂ : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hKK₄ : K ^ 2 ≤ K ^ 4 := by nlinarith [sq_nonneg (K ^ 2 - 1)]
  have hηq' : η ≤ q := by linarith
  have hfirst : |v| + 1 ≤ 2 * K ^ 2 := by linarith
  have habs : |-p - m * v| ≤ 3 * K + K ^ 2 := by
    calc
      _ ≤ |-p| + |m * v| := abs_sub _ _
      _ = |p| + |m| * |v| := by rw [abs_neg, abs_mul]
      _ ≤ 3 * K + 1 * K ^ 2 :=
        add_le_add hp (mul_le_mul hm hv (abs_nonneg _) zero_le_one)
      _ = _ := by rw [one_mul]
  have hsecond : |-p - m * v| + |m| + 1 ≤ 6 * K ^ 2 := by linarith
  constructor
  · exact (mul_le_mul hfirst hηq' hη (by positivity)).trans (by
      nlinarith [mul_nonneg (sq_nonneg K) hq])
  · calc
      _ ≤ (6 * K ^ 2) * q ^ 2 :=
        mul_le_mul hsecond hηq₂ hη (by positivity)
      _ ≤ _ := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hKK₄) (sq_nonneg q),
          mul_nonneg (sq_nonneg K) (sq_nonneg q)]

end Submission.Obl.k4_horizontal_strict_parameter_step
