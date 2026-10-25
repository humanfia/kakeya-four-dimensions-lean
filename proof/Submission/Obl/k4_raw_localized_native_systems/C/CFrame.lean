import Submission.Obl.k4_raw_localized_native_systems.C.CStrip

/-
Adapted from this LOT tree, o178, session x0596, `CFrame.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The frame of a full-time strip chart

For a unit normal `n` with tangent `e = rot90 n`, the frame with columns
`K' e` and `W n` has determinant `-K' W` and inverse with rows `e/K'`, `n/W`.
A displacement whose tangential component is at most `K'` and whose normal
component is at most `W` has inverse-frame norm at most `2`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The frame with columns `K' ⋅ rot90 n` and `W ⋅ n`. -/
def cFrame (K' W : ℝ) (n : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![K' * (-n 1), W * n 0; K' * n 0, W * n 1]

/-- Its inverse, with rows `rot90 n / K'` and `n / W`. -/
def cFrameInv (K' W : ℝ) (n : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(-n 1) / K', n 0 / K'; n 0 / W, n 1 / W]

theorem unit_sq {n : Plane} (hn : ‖n‖ = 1) : n 0 ^ 2 + n 1 ^ 2 = 1 := by
  have := norm_sq_fin2' n
  rw [hn] at this; linarith

theorem cFrame_det {n : Plane} (hn : ‖n‖ = 1) (K' W : ℝ) :
    (cFrame K' W n).det = -(K' * W) := by
  rw [Matrix.det_fin_two, cFrame]
  simp
  have := unit_sq hn
  linear_combination (-(K' * W)) * this

theorem cFrameInv_mul {n : Plane} (hn : ‖n‖ = 1) {K' W : ℝ} (hK : K' ≠ 0) (hW : W ≠ 0) :
    cFrameInv K' W n * cFrame K' W n = 1 := by
  have h := unit_sq hn
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cFrameInv, cFrame, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    nlinarith [h]

theorem cFrame_inv {n : Plane} (hn : ‖n‖ = 1) {K' W : ℝ} (hK : K' ≠ 0) (hW : W ≠ 0) :
    (cFrame K' W n)⁻¹ = cFrameInv K' W n :=
  Matrix.inv_eq_left_inv (cFrameInv_mul hn hK hW)

theorem cFrameInv_apply (K' W : ℝ) (n w : Plane) :
    Matrix.toEuclideanLin (cFrameInv K' W n) w =
      WithLp.toLp 2 ![inner ℝ (rot90 n) w / K', inner ℝ n w / W] := by
  ext i
  fin_cases i <;>
    simp [cFrameInv, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      inner_fin2] <;> ring

/-- Tangential and normal control give inverse-frame norm at most two. -/
theorem cFrame_bound {n : Plane} (hn : ‖n‖ = 1) {K' W : ℝ} (hK : 0 < K') (hW : 0 < W)
    {w : Plane} (h1 : |inner ℝ (rot90 n) w| ≤ K') (h2 : |inner ℝ n w| ≤ W) :
    ‖Matrix.toEuclideanLin (cFrame K' W n)⁻¹ w‖ ≤ 2 := by
  rw [cFrame_inv hn hK.ne' hW.ne', cFrameInv_apply]
  refine (norm_le_abs_add_abs_fin2 _).trans ?_
  have hz0 : (WithLp.toLp 2 ![inner ℝ (rot90 n) w / K', inner ℝ n w / W] : Plane) 0 =
      inner ℝ (rot90 n) w / K' := rfl
  have hz1 : (WithLp.toLp 2 ![inner ℝ (rot90 n) w / K', inner ℝ n w / W] : Plane) 1 =
      inner ℝ n w / W := rfl
  rw [hz0, hz1, abs_div, abs_div, abs_of_pos hK, abs_of_pos hW]
  have e1 : |inner ℝ (rot90 n) w| / K' ≤ 1 := by rw [div_le_one hK]; exact h1
  have e2 : |inner ℝ n w| / W ≤ 1 := by rw [div_le_one hW]; exact h2
  linarith

theorem norm_rot90_unit {n : Plane} (hn : ‖n‖ = 1) : ‖rot90 n‖ = 1 := by
  rw [norm_rot90, hn]

theorem inner_rot90_smul (n : Plane) (s : ℝ) : inner ℝ (rot90 n) (s • n) = 0 := by
  rw [inner_smul_right, inner_rot90_self, mul_zero]

/-- The frame bound for a line in a strip: the displacement from the moving centre
`int ⋅ n + t ⋅ speed ⋅ n` has tangential part `⟪rot90 n, y⟫` and normal part
`⟪n, y⟫ - int - t ⋅ speed`. -/
theorem cFrame_line_bound {n : Plane} (hn : ‖n‖ = 1) {K' W : ℝ} (hK : 0 < K') (hW : 0 < W)
    (int sp t : ℝ) (yt : Plane) (hy : ‖yt‖ ≤ K')
    (hstrip : |inner ℝ n yt - int - t * sp| ≤ W) :
    ‖Matrix.toEuclideanLin (cFrame K' W n)⁻¹ (yt - int • n - t • (sp • n))‖ ≤ 2 := by
  apply cFrame_bound hn hK hW
  · rw [inner_sub_right, inner_sub_right, inner_rot90_smul, smul_smul, inner_rot90_smul,
      sub_zero, sub_zero]
    exact (abs_inner_le_norm' _ _ (norm_rot90_unit hn)).trans hy
  · simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow,
      mul_one]
    exact hstrip

end

end Submission.Obl.k4_raw_localized_native_systems.C
