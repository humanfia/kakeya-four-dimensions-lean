-- Adapted from this LOT tree o173/x0598, commit b7284666,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/InitialScale.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.InitialScaleNumerics
import Submission.Obl.k4_clean_cover_graph_atlas.SelectedRootTransfer

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MvPolynomial Submission.Lib.K4QuadraticSheets

/-- The normalized selected equation and the physical derivative factor have
exactly the scale used in `initial_scale_bounds`. -/
theorem normalized_initial_scale_bounds {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) (flat : Bool) {A B a_fit : ℝ} (hA : 2 ≤ A) (hB : 0 < B)
    (ha_fit : a_fit ≤ 1) (u0 : Real3) (w0 : ℝ)
    (hclass : flat = false ↔ |qc P / 2| * a_fit ≤ A ^ (-20 : ℝ))
    (hlo : 4 * A ^ (-1 : ℝ) ≤ |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)|)
    (hhi : |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)| ≤ A) :
    let σ := eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P))
    let s := selectedSlopeFactor flat B * |σ|
    0 < s ∧ s ≤ B * A + B ^ 2 * |qc P| ∧ s⁻¹ ≤ A / B + A ^ (20 : ℕ) / B ^ 2 := by
  have hh := initial_scale_bounds flat hA hB ha_fit hclass hlo hhi
  have he : selectedSlopeFactor flat B *
      |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat P))| =
      if flat then B ^ 2 * |qc P| else
        B * |eval (Fin.snoc (fun j => u0 j) w0 : Fin 4 → ℝ) (pderiv 3 P)| := by
    cases flat
    · simp only [selectedSlopeFactor, selectedValueFactor, selectedSheetTest, Bool.coe_false,
        ite_false, mul_one]
    · rw [eval_selectedSheetSlope true hP]
      simp only [selectedSlopeFactor, selectedValueFactor, quadraticSheetSlope, Bool.coe_true, ite_true]
      rw [show 2 * (qc P / 2) = qc P by ring, pow_two]
  simpa only [he] using hh

end Submission.Obl.k4_clean_cover_graph_atlas
