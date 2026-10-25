/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ZoomScalar.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.CoefficientZoom
import Submission.Obl.k4_scalar_graph_residual_discovery.NormalStrips

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

def scalar (ρ : ℝ) (q : Fin 5 → ℤ) (F : ℝ → ℝ) (l : ScalarLine) (t : ℝ) : ℝ :=
  x ρ q l t - F t * y ρ q l t

def centeredNormal (ρ : ℝ) (q : Fin 5 → ℤ) (row : Fin 2 → ℝ) (l : ScalarLine) (t : ℝ) : ℝ :=
  (normalCoordinate row (scalarPosition (l, t)) -
    normalCoordinate row (scalarPosition (center ρ q, t))) / ρ

theorem measurable_scalar (ρ : ℝ) (q : Fin 5 → ℤ) {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun p : ScalarIncidence => scalar ρ q F p.1 p.2) := by
  unfold scalar x y coeff
  fun_prop

theorem abs_y_le_two {ρ : ℝ} (hρ : 0 < ρ) {q : Fin 5 → ℤ} {l : ScalarLine}
    (hl : cell ρ l.2 = q) {t : ℝ} (ht : |t| ≤ 1) : |y ρ q l t| ≤ 2 := by
  have hprod : |t * coeff ρ q l 4| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul ht (coeff_abs_le_one hρ hl 4)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  exact (abs_add_le _ _).trans (by
    have h := coeff_abs_le_one hρ hl 3
    linarith)

theorem abs_x_le_three {ρ : ℝ} (hρ : 0 < ρ) {q : Fin 5 → ℤ} {l : ScalarLine}
    (hl : cell ρ l.2 = q) {t : ℝ} (ht : |t| ≤ 1) : |x ρ q l t| ≤ 3 := by
  have ht₂ : |t ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hprod (v : ℝ) (hv : |v| ≤ 1) (e : Fin 5) : |v * coeff ρ q l e| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hv (coeff_abs_le_one hρ hl e)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  unfold x
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (by linarith [coeff_abs_le_one hρ hl 0, hprod t ht 1, hprod (t ^ 2) ht₂ 2])

theorem abs_scalar_le {ρ H : ℝ} (hρ : 0 < ρ) {q : Fin 5 → ℤ} {l : ScalarLine}
    (hl : cell ρ l.2 = q) {F : ℝ → ℝ} {t : ℝ} (ht : |t| ≤ 1) (hF : |F t| ≤ H) :
    |scalar ρ q F l t| ≤ 3 + 2 * H := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hF
  unfold scalar
  apply (abs_sub _ _).trans
  rw [abs_mul]
  have hprod := mul_le_mul hF (abs_y_le_two hρ hl ht) (abs_nonneg _) hH
  linarith [abs_x_le_three hρ hl ht]

theorem scalar_sub_centeredNormal (ρ : ℝ) (q : Fin 5 → ℤ) (row : Fin 2 → ℝ)
    (F : ℝ → ℝ) (l : ScalarLine) (t : ℝ) :
    scalar ρ q F l t - centeredNormal ρ q row l t = (row 1 - F t) * y ρ q l t := by
  unfold scalar centeredNormal
  rw [x_eq, y_eq]
  simp only [normalCoordinate, scalarPosition, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The scalar support is within a controlled error of the assigned
normal coordinate. The central-curve subtraction removes the large
original Y coordinate from the row-approximation error. -/
theorem scalar_near_assigned_normal {ρ b δ : ℝ} (hρ : 0 < ρ) (hb : 0 < b)
    (q : Fin 5 → ℤ) (row : Fin 2 → ℝ) (F : ℝ → ℝ) (l : ScalarLine) (t : ℝ)
    (hl : cell ρ l.2 = q) (ht : |t| ≤ 1) (hrow : |row 1 - F t| ≤ δ) :
    |scalar ρ q F l t -
      (normalCoordinate row (leftCorner b (cell b (scalarPosition (l, t)))) -
        normalCoordinate row (scalarPosition (center ρ q, t))) / ρ| ≤
      2 * δ + (1 + |row 0| + |row 1|) * b / ρ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hrow
  have hfirst : |scalar ρ q F l t - centeredNormal ρ q row l t| ≤ 2 * δ := by
    rw [scalar_sub_centeredNormal, abs_mul]
    exact (mul_le_mul hrow (abs_y_le_two hρ hl ht) (abs_nonneg _) hδ).trans_eq (by ring)
  have hsecond : |centeredNormal ρ q row l t -
      (normalCoordinate row (leftCorner b (cell b (scalarPosition (l, t)))) -
        normalCoordinate row (scalarPosition (center ρ q, t))) / ρ| ≤
      (1 + |row 0| + |row 1|) * b / ρ := by
    rw [show centeredNormal ρ q row l t -
      (normalCoordinate row (leftCorner b (cell b (scalarPosition (l, t)))) -
        normalCoordinate row (scalarPosition (center ρ q, t))) / ρ =
      (normalCoordinate row (scalarPosition (l, t)) -
        normalCoordinate row (leftCorner b (cell b (scalarPosition (l, t))))) / ρ by
          unfold centeredNormal; ring, abs_div, abs_of_pos hρ]
    exact div_le_div_of_nonneg_right (normalCoordinate_center_error hb row _) hρ.le
  exact (abs_sub_le _ (centeredNormal ρ q row l t) _).trans (add_le_add hfirst hsecond)

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
