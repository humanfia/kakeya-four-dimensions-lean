-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_cinematic_jet_bounds.Algebra.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_normalized_cinematic_jet_bounds

/-- Recover coefficients from the value, first derivative, and second derivative. -/
lemma coefficients_le_jet (a b d z v w t : ℝ)
    (hz : |z| ≤ 1) (hv : |v| ≤ 3) (hw : 1 ≤ |w|) (ht : |t| ≤ 1 / 100) :
    |a| + |b| + |d| ≤ 30 *
      (|a + (b + d * z) * v| + |(b + d * z) * w + d * v| +
        |(b + d * z) * t + 2 * d * w|) := by
  let U := b + d * z
  change |a| + |b| + |d| ≤ 30 *
    (|a + U * v| + |U * w + d * v| + |U * t + 2 * d * w|)
  have hU : |U| ≤ |U * w + d * v| + 3 * |d| := by
    calc
      |U| ≤ |U| * |w| := by nlinarith [abs_nonneg U]
      _ = |(U * w + d * v) - d * v| := by rw [← abs_mul]; congr 1; ring
      _ ≤ |U * w + d * v| + |d * v| := abs_sub _ _
      _ ≤ |U * w + d * v| + 3 * |d| := by
        rw [abs_mul]
        nlinarith [abs_nonneg d]
  have hD : 2 * |d| ≤ |U * t + 2 * d * w| + |U| / 100 := by
    calc
      2 * |d| ≤ |2 * d * w| := by
        rw [abs_mul, abs_mul]
        norm_num
        nlinarith [abs_nonneg d]
      _ = |(U * t + 2 * d * w) - U * t| := by congr 1; ring
      _ ≤ |U * t + 2 * d * w| + |U * t| := abs_sub _ _
      _ ≤ |U * t + 2 * d * w| + |U| / 100 := by
        rw [abs_mul]
        nlinarith [abs_nonneg U]
  have hd : |d| ≤ |U * w + d * v| + |U * t + 2 * d * w| := by
    linarith [abs_nonneg (U * w + d * v), abs_nonneg (U * t + 2 * d * w)]
  have hb : |b| ≤ |U| + |d| := by
    calc
      |b| = |U - d * z| := by dsimp [U]; rw [add_sub_cancel_right]
      _ ≤ |U| + |d * z| := abs_sub _ _
      _ ≤ |U| + |d| := by rw [abs_mul]; nlinarith [abs_nonneg d]
  have ha : |a| ≤ |a + U * v| + 3 * |U| := by
    calc
      |a| = |(a + U * v) - U * v| := by rw [add_sub_cancel_right]
      _ ≤ |a + U * v| + |U * v| := abs_sub _ _
      _ ≤ |a + U * v| + 3 * |U| := by rw [abs_mul]; nlinarith [abs_nonneg U]
  linarith [abs_nonneg (a + U * v), abs_nonneg (U * w + d * v),
    abs_nonneg (U * t + 2 * d * w)]

/-- Each coordinate is at most the Euclidean norm, giving the forward jet estimate. -/
lemma jet_le_bound (a b d z v w t D : ℝ)
    (hz : |z| ≤ 1) (hv : |v| ≤ 3) (hw : |w| ≤ 2) (ht : |t| ≤ 1 / 100)
    (ha : |a| ≤ D) (hb : |b| ≤ D) (hd : |d| ≤ D) :
    |a + (b + d * z) * v| + |(b + d * z) * w + d * v| +
      |(b + d * z) * t + 2 * d * w| ≤ 19 * D := by
  let U := b + d * z
  change |a + U * v| + |U * w + d * v| + |U * t + 2 * d * w| ≤ 19 * D
  have hD : 0 ≤ D := (abs_nonneg a).trans ha
  have hU : |U| ≤ 2 * D := by
    have h := abs_add_le b (d * z)
    rw [abs_mul] at h
    dsimp [U]
    nlinarith [abs_nonneg d]
  have huv : |U * v| ≤ 6 * D := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hv (abs_nonneg U)]
  have huw : |U * w| ≤ 4 * D := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hw (abs_nonneg U)]
  have hdv : |d * v| ≤ 3 * D := by
    rw [abs_mul]
    nlinarith [abs_nonneg d]
  have hut : |U * t| ≤ D / 50 := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg U)]
  have hdw : |2 * d * w| ≤ 4 * D := by
    rw [abs_mul, abs_mul]
    norm_num
    nlinarith [abs_nonneg d]
  have hA := abs_add_le a (U * v)
  have hB := abs_add_le (U * w) (d * v)
  have hC := abs_add_le (U * t) (2 * d * w)
  linarith

lemma norm_le_abs_sum (q : EuclideanSpace ℝ (Fin 3)) :
    ‖q‖ ≤ |q 0| + |q 1| + |q 2| := by
  have h : ‖q‖ ^ 2 = |q 0| ^ 2 + (|q 1| ^ 2 + |q 2| ^ 2) := by
    simpa [Fin.sum_univ_succ, Real.norm_eq_abs] using EuclideanSpace.norm_sq_eq q
  apply (sq_le_sq₀ (norm_nonneg q) (by positivity)).mp
  nlinarith [
    mul_nonneg (abs_nonneg (q 0)) (abs_nonneg (q 1)),
    mul_nonneg (abs_nonneg (q 0)) (abs_nonneg (q 2)),
    mul_nonneg (abs_nonneg (q 1)) (abs_nonneg (q 2))]

end WangZahlLot.Obl.wz_normalized_cinematic_jet_bounds
