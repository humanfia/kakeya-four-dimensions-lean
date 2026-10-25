import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.ScalarClosure

/-!
# The scalar-closure loss is a fixed monomial

Once the expression lengths are fixed, the support bound has a fixed degree in the input
loss. Recording that degree makes the final choice of the small input exponent explicit.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity.ClosureData

/-- The product-closure multiplier is a monomial in the input loss. -/
theorem Bn_monomial (K : ℝ) (a n : ℕ) :
    Bn K a n = Bn 1 a n * K ^ (4 * n + 2 * a + (4 * a + 8) * n + 3 * a) := by
  have hpow : K ^ (4 * n + 2 * a + (4 * a + 8) * n + 3 * a) =
      K ^ (4 * n + 2 * a) * (K ^ (4 * a + 8)) ^ n * K ^ (3 * a) := by
    rw [pow_add, pow_add, pow_mul]
  simp only [Bn, M1, one_pow, mul_one, mul_pow]
  rw [hpow]
  ring

/-- The degree of the generated-coefficient support bound in the input loss. -/
def closureDegree (a m k n : ℕ) : ℕ :=
  (4 * n + 2 * a + (4 * a + 8) * n + 3 * a + a) * (m * (k * 2)) +
    (4 * a) * (2 * (m * (k * 2))) + a

/-- Every fixed generated-support constant is exactly a fixed coefficient times a fixed power. -/
theorem closureConst_monomial (K : ℝ) (a m k n : ℕ) :
    closureConst K a m k n = closureConst 1 a m k n * K ^ closureDegree a m k n := by
  let d := m * (k * 2)
  let b := 4 * n + 2 * a + (4 * a + 8) * n + 3 * a
  have hpow : K ^ closureDegree a m k n =
      (K ^ b * K ^ a) ^ d * (K ^ (4 * a)) ^ (2 * d) * K ^ a := by
    change K ^ ((b + a) * d + (4 * a) * (2 * d) + a) = _
    rw [pow_add, pow_add, pow_mul K (b + a) d, pow_mul K (4 * a) (2 * d), pow_add K b a]
  unfold closureConst
  rw [Bn_monomial K a n]
  simp only [hpow, one_pow, mul_one, mul_pow]
  dsimp [b, d]
  ring

theorem closureConst_one_pos (a m k n : ℕ) : 0 < closureConst 1 a m k n := by
  unfold closureConst Bn M1
  positivity

/-- Specializing the fixed polynomial loss to a small negative power of the mesh. -/
theorem closureConst_rpow {h : ℝ} (hh : 0 < h) (η : ℝ) (A a m k n : ℕ) :
    closureConst ((h ^ (-η)) ^ A) a m k n =
      closureConst 1 a m k n * h ^ (-η * ((A * closureDegree a m k n : ℕ) : ℝ)) := by
  rw [closureConst_monomial, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hh.le]

end Submission.Obl.k4_retained_edge_planar_rigidity.ClosureData
