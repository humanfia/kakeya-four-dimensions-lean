-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.Removal

/-!
# Planar geometry for strips

Coordinates in `EuclideanSpace ℝ (Fin 2)`, the rotation by a right angle, and
the basic closeness lemma: two unit vectors that are both nearly orthogonal to a
unit vector `u`, and on the same side of it, are close.

Ported from session x0394 (o141, commit d684c60).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

lemma inner_coords (x y : E2) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma norm_sq_coords (x : E2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]

/-- The rotation by a right angle. -/
noncomputable def rot (u : E2) : E2 := !₂[-(u 1), u 0]

@[simp] lemma rot_zero (u : E2) : rot u 0 = -(u 1) := rfl
@[simp] lemma rot_one (u : E2) : rot u 1 = u 0 := rfl

/-- Pythagoras in the frame `(u, rot u)`. -/
lemma norm_sq_frame {u : E2} (hu : ‖u‖ = 1) (x : E2) :
    ‖x‖ ^ 2 = (inner ℝ x u) ^ 2 + (inner ℝ x (rot u)) ^ 2 := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_coords, hu]; norm_num
  rw [norm_sq_coords, inner_coords, inner_coords, rot_zero, rot_one]
  have : (x 0 * u 0 + x 1 * u 1) ^ 2 + (x 0 * -u 1 + x 1 * u 0) ^ 2 =
      (x 0 ^ 2 + x 1 ^ 2) * (u 0 ^ 2 + u 1 ^ 2) := by ring
  rw [this, hu2, mul_one]

/-- Two unit vectors nearly orthogonal to `u` and on the same side of it are close. -/
lemma frame_close {u e e' : E2} (hu : ‖u‖ = 1) (he : ‖e‖ = 1) (he' : ‖e'‖ = 1)
    (ha : (inner ℝ e u) ^ 2 ≤ 1 / 2) (ha' : (inner ℝ e' u) ^ 2 ≤ 1 / 2)
    (hb : 0 ≤ inner ℝ e (rot u) * inner ℝ e' (rot u)) :
    ‖e - e'‖ ^ 2 ≤ 3 * (inner ℝ e u - inner ℝ e' u) ^ 2 := by
  have h1 := norm_sq_frame hu e
  have h2 := norm_sq_frame hu e'
  have h3 := norm_sq_frame hu (e - e')
  rw [he] at h1; rw [he'] at h2
  rw [inner_sub_left, inner_sub_left] at h3
  set a := inner ℝ e u
  set b := inner ℝ e (rot u)
  set a' := inner ℝ e' u
  set b' := inner ℝ e' (rot u)
  rw [h3]
  have key : (b - b') ^ 2 * (b + b') ^ 2 = (a - a') ^ 2 * (a + a') ^ 2 := by
    have : b ^ 2 - b' ^ 2 = a' ^ 2 - a ^ 2 := by nlinarith
    calc (b - b') ^ 2 * (b + b') ^ 2 = (b ^ 2 - b' ^ 2) ^ 2 := by ring
      _ = (a' ^ 2 - a ^ 2) ^ 2 := by rw [this]
      _ = (a - a') ^ 2 * (a + a') ^ 2 := by ring
  have hbb : 1 ≤ (b + b') ^ 2 := by nlinarith
  have haa : (a + a') ^ 2 ≤ 2 := by nlinarith [sq_nonneg (a - a')]
  have hd : 0 ≤ (b - b') ^ 2 := sq_nonneg _
  have : (b - b') ^ 2 ≤ 2 * (a - a') ^ 2 := by
    calc (b - b') ^ 2 ≤ (b - b') ^ 2 * (b + b') ^ 2 := le_mul_of_one_le_right hd hbb
      _ = (a - a') ^ 2 * (a + a') ^ 2 := key
      _ ≤ (a - a') ^ 2 * 2 := mul_le_mul_of_nonneg_left haa (sq_nonneg _)
      _ = 2 * (a - a') ^ 2 := by ring
  linarith

lemma abs_inner_le_norm_mul {x y : E2} : |inner ℝ x y| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y

lemma norm_le_eight_of_norm_le_four {x y : E2} (hx : ‖x‖ ≤ 4) (hy : ‖y‖ ≤ 4) : ‖x - y‖ ≤ 8 := by
  calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
    _ ≤ 8 := by linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
