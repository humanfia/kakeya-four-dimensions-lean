-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/SelectedRootTransfer.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/SelectedRootTransfer.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.NormalizedSheetChoice
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.PacketRootTransfer

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial Submission.Lib.K4XInterface

/-- The positive value factor for the original selected equation. -/
noncomputable def selectedValueFactor (flat : Bool) (B : ℝ) : ℝ := if flat then B else 1

/-- The derivative of the original selected equation has this factor relative to
its normalized counterpart. -/
noncomputable def selectedSlopeFactor (flat : Bool) (B : ℝ) : ℝ :=
  B * selectedValueFactor flat B

theorem selectedValueFactor_pos (flat : Bool) {B : ℝ} (hB : 0 < B) :
    0 < selectedValueFactor flat B := by
  cases flat
  · norm_num [selectedValueFactor]
  · simpa only [selectedValueFactor, Bool.coe_true, ite_true] using hB

theorem selectedSlopeFactor_pos (flat : Bool) {B : ℝ} (hB : 0 < B) :
    0 < selectedSlopeFactor flat B := mul_pos hB (selectedValueFactor_pos flat hB)

/-- Both kinds of normalized root give a root of the corresponding original test. -/
theorem eval_selected_original_hidden_update (flat : Bool) {T j : ℕ}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ}
    (hQ : Q.det ≠ 0) (hB : B ≠ 0) (R : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t w : ℝ) :
    eval (Function.update (gx l t) (3 : Fin 4) (w / B)) (selectedSheetTest flat R) =
      selectedValueFactor flat B *
        eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
          (selectedSheetTest flat (normPoly T j c u Q B R)) := by
  cases flat
  · simpa only [selectedSheetTest, selectedValueFactor, Bool.coe_false, ite_false, one_mul] using
      (eval_normPoly_hidden_update hQ hB R l t w).symm
  · simp only [selectedSheetTest, selectedValueFactor, Bool.coe_true, ite_true]
    rw [eval_pderiv_normPoly_hidden_update hQ hB]
    field_simp

/-- The exact derivative factor includes the extra normalization factor when the
selected sheet is the affine hidden derivative. -/
theorem eval_selected_original_slope_hidden_update (flat : Bool) {T j : ℕ}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ}
    (hQ : Q.det ≠ 0) (hB : B ≠ 0) (R : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t w : ℝ) :
    eval (Function.update (gx l t) (3 : Fin 4) (w / B)) (pderiv 3 (selectedSheetTest flat R)) =
      selectedSlopeFactor flat B *
        eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
          (pderiv 3 (selectedSheetTest flat (normPoly T j c u Q B R))) := by
  cases flat
  · simp only [selectedSheetTest, selectedSlopeFactor, selectedValueFactor,
      Bool.coe_false, ite_false, mul_one]
    rw [eval_pderiv_normPoly_hidden_update hQ hB]
    field_simp
  · simp only [selectedSheetTest, selectedSlopeFactor, selectedValueFactor, Bool.coe_true, ite_true]
    rw [pderiv_normPoly, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul,
      map_mul, eval_C, eval_pderiv_normPoly_hidden_update hQ hB]
    field_simp

/-- Root equations, the narrow absolute derivative window and the chosen derivative
sign transfer together to the original polynomial and original base point. -/
theorem selected_root_physical_certificate (flat : Bool) {T j : ℕ}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ}
    (hQ : Q.det ≠ 0) (hB : 0 < B) (R : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t w σ : ℝ)
    (hroot : eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
      (selectedSheetTest flat (normPoly T j c u Q B R)) = 0)
    (hlo : 19 / 20 * |σ| ≤ |eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
      (pderiv 3 (selectedSheetTest flat (normPoly T j c u Q B R)))|)
    (hhi : |eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
      (pderiv 3 (selectedSheetTest flat (normPoly T j c u Q B R)))| ≤ 21 / 20 * |σ|)
    (hsign : 0 < eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
      (pderiv 3 (selectedSheetTest flat (normPoly T j c u Q B R))) * σ) :
    let k := selectedSlopeFactor flat B
    let v := Function.update (gx l t) (3 : Fin 4) (w / B)
    eval v (selectedSheetTest flat R) = 0 ∧
      19 / 20 * (k * |σ|) ≤ |eval v (pderiv 3 (selectedSheetTest flat R))| ∧
      |eval v (pderiv 3 (selectedSheetTest flat R))| ≤ 21 / 20 * (k * |σ|) ∧
      0 < eval v (pderiv 3 (selectedSheetTest flat R)) * (k * σ) := by
  dsimp only
  rw [eval_selected_original_hidden_update flat hQ hB.ne', hroot, mul_zero,
    eval_selected_original_slope_hidden_update flat hQ hB.ne']
  have hk := selectedSlopeFactor_pos flat hB
  rw [abs_mul, abs_of_pos hk]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · calc
      _ = selectedSlopeFactor flat B * (19 / 20 * |σ|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hk.le
  · calc
      _ ≤ selectedSlopeFactor flat B * (21 / 20 * |σ|) := mul_le_mul_of_nonneg_left hhi hk.le
      _ = _ := by ring
  · convert mul_pos (sq_pos_of_pos hk) hsign using 1 <;> ring

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
