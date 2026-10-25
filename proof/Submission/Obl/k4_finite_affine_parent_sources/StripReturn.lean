-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.Original
import Submission.Lib.K4XInterface.Charts

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4XInterface

noncomputable section

/-- The pullback of a scalar slope strip has this row in the old frame. -/
def stripRow (M : Matrix (Fin 2) (Fin 2) ℝ) (slope : ℝ) : Fin 2 → ℝ :=
  ![M 1 0 - slope * M 0 0, M 1 1 - slope * M 0 1]

def stripRowLength (M : Matrix (Fin 2) (Fin 2) ℝ) (slope : ℝ) : ℝ :=
  Real.sqrt ((stripRow M slope 0) ^ 2 + (stripRow M slope 1) ^ 2)

/-- The slope cancels from the determinant identity. -/
theorem stripRow_det (M : Matrix (Fin 2) (Fin 2) ℝ) (slope : ℝ) :
    stripRow M slope 1 * M 0 0 - stripRow M slope 0 * M 0 1 = M.det := by
  simp only [stripRow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.det_fin_two]
  ring

theorem stripRowLength_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0) (slope : ℝ) :
    0 < stripRowLength M slope := by
  apply Real.sqrt_pos.mpr
  by_contra h
  have heq : (stripRow M slope 0) ^ 2 + (stripRow M slope 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (stripRow M slope 0), sq_nonneg (stripRow M slope 1)]
  have h0 : stripRow M slope 0 = 0 := by nlinarith [sq_nonneg (stripRow M slope 1)]
  have h1 : stripRow M slope 1 = 0 := by nlinarith [sq_nonneg (stripRow M slope 0)]
  apply hM
  rw [← stripRow_det M slope, h0, h1]
  ring

theorem stripRowLength_sq (M : Matrix (Fin 2) (Fin 2) ℝ) (slope : ℝ) :
    (stripRowLength M slope) ^ 2 =
      (stripRow M slope 0) ^ 2 + (stripRow M slope 1) ^ 2 := by
  apply Real.sq_sqrt
  positivity

theorem stripRow_abs_le_length (M : Matrix (Fin 2) (Fin 2) ℝ) (slope : ℝ) (e : Fin 2) :
    |stripRow M slope e| ≤ stripRowLength M slope := by
  apply abs_le.mpr
  apply abs_le_of_sq_le_sq' _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by positivity)]
  fin_cases e
  · change (stripRow M slope 0) ^ 2 ≤
      (stripRow M slope 0) ^ 2 + (stripRow M slope 1) ^ 2
    linarith only [sq_nonneg (stripRow M slope 1)]
  · change (stripRow M slope 1) ^ 2 ≤
      (stripRow M slope 0) ^ 2 + (stripRow M slope 1) ^ 2
    linarith only [sq_nonneg (stripRow M slope 0)]

/-- Determinant control gives the quantitative lower bound on the row's
length needed to cancel the true transverse width. -/
theorem det_le_stripRowLength (M : Matrix (Fin 2) (Fin 2) ℝ) (slope : ℝ)
    (B : ℝ) (hB : |M 0 0| + |M 0 1| ≤ B) :
    |M.det| ≤ stripRowLength M slope * B := by
  rw [← stripRow_det M slope]
  calc
    _ ≤ |stripRow M slope 1 * M 0 0| + |stripRow M slope 0 * M 0 1| := abs_sub _ _
    _ = |stripRow M slope 1| * |M 0 0| + |stripRow M slope 0| * |M 0 1| := by
      rw [abs_mul, abs_mul]
    _ ≤ stripRowLength M slope * |M 0 0| + stripRowLength M slope * |M 0 1| := by
      gcongr
      · exact stripRow_abs_le_length M slope 1
      · exact stripRow_abs_le_length M slope 0
    _ = stripRowLength M slope * (|M 0 0| + |M 0 1|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)

/-- Pull back a slope strip by an arbitrary invertible affine velocity
change, producing a unit normal and an explicit bias bound. -/
theorem slope_strip_return
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (offset : Fin 2 → ℝ) (z : Fin 2 → ℝ) (width : ℝ) :
    ∃ (a : Fin 2 → ℝ) (bias : ℝ), (∑ e, (a e) ^ 2) = 1 ∧
      |bias| ≤ (|z 0| + |offset 1| + |z 1| * |offset 0|) / stripRowLength M (z 1) ∧
      ∀ (w wm : Fin 2 → ℝ),
        (∀ e, wm e = offset e + ∑ f, M e f * w f) →
        |wm 1 - z 0 - z 1 * wm 0| ≤ width →
        |(∑ e, a e * w e) - bias| ≤ width / stripRowLength M (z 1) := by
  let D := stripRowLength M (z 1)
  have hD : 0 < D := stripRowLength_pos M hM (z 1)
  refine ⟨fun e => stripRow M (z 1) e / D,
    (z 0 - offset 1 + z 1 * offset 0) / D, ?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_two, div_pow]
    rw [← add_div, ← stripRowLength_sq]
    exact div_self (pow_ne_zero 2 hD.ne')
  · rw [abs_div, abs_of_pos hD]
    apply div_le_div_of_nonneg_right _ hD.le
    calc
      |z 0 - offset 1 + z 1 * offset 0|
        = |(z 0 - offset 1) + z 1 * offset 0| := by ring_nf
      _ ≤ |z 0 - offset 1| + |z 1 * offset 0| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul]; linarith only [abs_sub (z 0) (offset 1)]
  · intro w wm hwm hstrip
    have heq : (∑ e, stripRow M (z 1) e / D * w e) -
        (z 0 - offset 1 + z 1 * offset 0) / D =
        (wm 1 - z 0 - z 1 * wm 0) / D := by
      rw [hwm 0, hwm 1]
      simp only [Fin.sum_univ_two, stripRow, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [heq, abs_div, abs_of_pos hD]
    exact div_le_div_of_nonneg_right hstrip hD.le

end

end Submission.Obl.k4_finite_affine_parent_sources
