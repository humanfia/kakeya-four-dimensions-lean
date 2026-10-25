import Submission.Obl.k4_raw_localized_native_systems.C.CFrame

/-
Adapted from this LOT tree, o178, session x0596, `StripFrame.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The unit-tangent frame of a full-time strip

For a unit normal `n`, the tangent is `e = (n 1, -n 0)` (so that `rot90 e = n`), and
the frame of normal width `g` has columns `e` and `g ⋅ n`.  It is written with the
coordinates `stripTangent n = (0, n 1, -n 0)` of the scalar projection, exactly as
in the split interface of the parent.  A displacement whose norm is at most `K'`
and whose normal component is at most `g` has inverse-frame norm at most `K' + 1`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The tangent coordinates `(0, e)` of a strip with unit normal `n`. -/
def stripTangent (n : Plane) : Fin 3 → ℝ := ![0, n 1, -n 0]

/-- The frame with columns `e` and `g ⋅ n`. -/
def stripFrame (g : ℝ) (n : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![stripTangent n 1, -g * stripTangent n 2; stripTangent n 2, g * stripTangent n 1]

/-- Its inverse, with rows `e` and `n / g`. -/
def stripFrameInv (g : ℝ) (n : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![n 1, -n 0; n 0 / g, n 1 / g]

@[simp] theorem stripTangent_zero (n : Plane) : stripTangent n 0 = 0 := rfl
@[simp] theorem stripTangent_one (n : Plane) : stripTangent n 1 = n 1 := rfl
@[simp] theorem stripTangent_two (n : Plane) : stripTangent n 2 = -n 0 := rfl

theorem stripTangent_unit {n : Plane} (hn : ‖n‖ = 1) :
    stripTangent n 1 ^ 2 + stripTangent n 2 ^ 2 = 1 := by
  have := unit_sq hn
  simp only [stripTangent_one, stripTangent_two, neg_sq]
  linarith

/-- The literal form used by the split interface. -/
theorem stripFrame_eq_literal (g : ℝ) (n : Plane) :
    stripFrame g n = ![![stripTangent n 1, -g * stripTangent n 2],
      ![stripTangent n 2, g * stripTangent n 1]] := rfl

theorem stripFrame_apply (g : ℝ) (n : Plane) :
    stripFrame g n = !![n 1, g * n 0; -n 0, g * n 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stripFrame]

theorem stripFrame_det {n : Plane} (hn : ‖n‖ = 1) (g : ℝ) : (stripFrame g n).det = g := by
  rw [stripFrame_apply, Matrix.det_fin_two]
  simp
  have := unit_sq hn
  linear_combination g * this

theorem stripFrameInv_mul {n : Plane} (hn : ‖n‖ = 1) {g : ℝ} (hg : g ≠ 0) :
    stripFrameInv g n * stripFrame g n = 1 := by
  have h := unit_sq hn
  rw [stripFrame_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stripFrameInv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    nlinarith [h]

theorem stripFrame_inv {n : Plane} (hn : ‖n‖ = 1) {g : ℝ} (hg : g ≠ 0) :
    (stripFrame g n)⁻¹ = stripFrameInv g n :=
  Matrix.inv_eq_left_inv (stripFrameInv_mul hn hg)

theorem stripFrameInv_apply (g : ℝ) (n w : Plane) :
    Matrix.toEuclideanLin (stripFrameInv g n) w =
      WithLp.toLp 2 ![n 1 * w 0 - n 0 * w 1, inner ℝ n w / g] := by
  ext i
  fin_cases i <;>
    simp [stripFrameInv, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      inner_fin2] <;> ring

/-- The tangential coordinate is at most the norm. -/
theorem abs_tangential_le {n : Plane} (hn : ‖n‖ = 1) (w : Plane) :
    |n 1 * w 0 - n 0 * w 1| ≤ ‖w‖ := by
  have h1 := unit_sq hn
  have h2 := norm_sq_fin2' w
  have hsq : (n 1 * w 0 - n 0 * w 1) ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [h2]
    nlinarith [sq_nonneg (n 0 * w 0 + n 1 * w 1)]
  exact abs_le_of_sq_le_sq hsq (norm_nonneg _)

/-- **The strip-frame bound.** -/
theorem stripFrame_bound {n : Plane} (hn : ‖n‖ = 1) {g : ℝ} (hg : 0 < g) {w : Plane} {K' W : ℝ}
    (h1 : |n 1 * w 0 - n 0 * w 1| ≤ K') (h2 : |inner ℝ n w| ≤ g * W) :
    ‖Matrix.toEuclideanLin (stripFrame g n)⁻¹ w‖ ≤ K' + W := by
  rw [stripFrame_inv hn hg.ne', stripFrameInv_apply]
  refine (norm_le_abs_add_abs_fin2 _).trans ?_
  have hz0 : (WithLp.toLp 2 ![n 1 * w 0 - n 0 * w 1, inner ℝ n w / g] : Plane) 0 =
      n 1 * w 0 - n 0 * w 1 := rfl
  have hz1 : (WithLp.toLp 2 ![n 1 * w 0 - n 0 * w 1, inner ℝ n w / g] : Plane) 1 =
      inner ℝ n w / g := rfl
  rw [hz0, hz1, abs_div, abs_of_pos hg]
  have e2 : |inner ℝ n w| / g ≤ W := by
    rw [div_le_iff₀ hg]; linarith
  linarith

/-- The frame bound for a line of a full-time strip with purely normal centre and
velocity. -/
theorem stripFrame_line_bound {n : Plane} (hn : ‖n‖ = 1) {g : ℝ} (hg : 0 < g)
    (int sp t : ℝ) (yt : Plane) {K' : ℝ} (hy : ‖yt‖ ≤ K')
    (hstrip : |inner ℝ n yt - int - t * sp| ≤ g) :
    ‖Matrix.toEuclideanLin (stripFrame g n)⁻¹ (yt - int • n - t • (sp • n))‖ ≤ K' + 1 := by
  apply stripFrame_bound hn hg
  · have heq : n 1 * (yt - int • n - t • (sp • n)) 0 - n 0 * (yt - int • n - t • (sp • n)) 1 =
        n 1 * yt 0 - n 0 * yt 1 := by
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact (abs_tangential_le hn yt).trans hy
  · simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow,
      mul_one]
    linarith [hstrip]

end

end Submission.Obl.k4_raw_localized_native_systems.C
