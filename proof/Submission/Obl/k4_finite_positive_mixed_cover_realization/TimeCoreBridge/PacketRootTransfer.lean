-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/PacketRootTransfer.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PacketRootTransfer.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.PacketCoords

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial Submission.Lib.K4XInterface

/-- The packet substitution commutes with changing only the hidden coordinate. -/
theorem packetSubst_hidden_update (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (v : Fin 4 → ℝ) (w : ℝ) :
    (fun i => eval (Function.update v (3 : Fin 4) w) (packetSubst T j c u Q B i)) =
      Function.update (fun i => eval v (packetSubst T j c u Q B i)) (3 : Fin 4) (B⁻¹ * w) := by
  funext i
  fin_cases i <;> simp [packetSubst, Function.update]

/-- A normalized root over a line's base is a root over the same original base,
with the hidden coordinate divided by the fixed world scale. -/
theorem eval_normPoly_hidden_update {T j : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hQ : Q.det ≠ 0) (hB : B ≠ 0)
    (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t w : ℝ) :
    eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
      (normPoly T j c u Q B R) =
      eval (Function.update (gx l t) (3 : Fin 4) (w / B)) R := by
  rw [eval_normPoly, packetSubst_hidden_update, packetSubst_normPt hQ hB]
  rw [show B⁻¹ * w = w / B by ring]

/-- The hidden derivative scale at a normalized root converts without any change
of the original trajectory or time. -/
theorem eval_pderiv_normPoly_hidden_update {T j : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hQ : Q.det ≠ 0) (hB : B ≠ 0)
    (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t w : ℝ) :
    eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
      (pderiv 3 (normPoly T j c u Q B R)) =
      B⁻¹ * eval (Function.update (gx l t) (3 : Fin 4) (w / B)) (pderiv 3 R) := by
  rw [pderiv_normPoly, map_mul, eval_C, eval_normPoly_hidden_update hQ hB]

/-- Dividing the hidden coordinate by the fixed world scale divides the fitting
error by exactly the same factor. -/
theorem packet_hidden_fit_transfer {B η : ℝ} (hB : 0 < B) {x w : ℝ}
    (hfit : |B * x - w| ≤ η) : |x - w / B| ≤ η / B := by
  have he : x - w / B = (B * x - w) / B := by field_simp [hB.ne']
  rw [he, abs_div, abs_of_pos hB]
  exact div_le_div_of_nonneg_right hfit hB.le

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
