-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/NormalizedBounds.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/NormalizedBounds.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.RegionGeometry

/-!
# Test bounds in normalized packet coordinates

Original hidden test bounds of the form `|R| ≤ a δ`, `|∂_w R| ≤ a B`, `|∂²_w R| ≤ a B²/δ` along a
line become the `B`-free bounds `|P̃| ≤ a δ`, `|∂_w̃ P̃| ≤ a`, `|qc P̃| ≤ a/δ` for the normalized test
`P̃ = normPoly R` at the normalized point (`normalized_bounds`), and a lower bound
`B / a ≤ |∂_w R|` becomes `1/a ≤ |∂_w̃ P̃|` (`normalized_lower`).
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

theorem normalized_bounds {T j : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hQ : Q.det ≠ 0) (hB : 0 < B)
    {R : MvPolynomial (Fin 4) ℝ} (hR : R.totalDegree ≤ 2) {a δ' : ℝ} (hδ : 0 < δ')
    {l : ℕ × (Fin 6 → ℝ)} {t : ℝ}
    (h0 : |eval (gx l t) R| ≤ a * δ')
    (h1 : |eval (gx l t) (pderiv 3 R)| ≤ a * B)
    (h2 : |eval (gx l t) (pderiv 3 (pderiv 3 R))| ≤ a * B ^ 2 / δ') :
    |eval (normPt T j c u Q B l t) (normPoly T j c u Q B R)| ≤ a * δ' ∧
      |eval (normPt T j c u Q B l t) (pderiv 3 (normPoly T j c u Q B R))| ≤ a ∧
      |qc (normPoly T j c u Q B R)| ≤ a / δ' := by
  obtain ⟨e0, e1⟩ := normPt_tests (T := T) (j := j) (c := c) (u := u) hQ hB.ne' R l t
  refine ⟨by rw [e0]; exact h0, ?_, ?_⟩
  · rw [e1, abs_mul, abs_inv, abs_of_pos hB, inv_mul_le_iff₀ hB]
    linarith
  · rw [qc_normPoly hR]
    have hq : qc R = eval (gx l t) (pderiv 3 (pderiv 3 R)) :=
      (eval_pderiv2_eq_qc (n := 3) R hR (gx l t)).symm
    rw [hq, abs_mul, abs_mul, abs_inv, abs_of_pos hB]
    have hB2 : 0 < B ^ 2 := by positivity
    calc B⁻¹ * B⁻¹ * |eval (gx l t) (pderiv 3 (pderiv 3 R))|
        ≤ B⁻¹ * B⁻¹ * (a * B ^ 2 / δ') :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = a / δ' := by field_simp

theorem normalized_lower {T j : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ} (hQ : Q.det ≠ 0) (hB : 0 < B)
    {R : MvPolynomial (Fin 4) ℝ} {a : ℝ} (ha : 0 < a) {l : ℕ × (Fin 6 → ℝ)} {t : ℝ}
    (h : B / a ≤ |eval (gx l t) (pderiv 3 R)|) :
    1 / a ≤ |eval (normPt T j c u Q B l t) (pderiv 3 (normPoly T j c u Q B R))| := by
  obtain ⟨-, e1⟩ := normPt_tests (T := T) (j := j) (c := c) (u := u) hQ hB.ne' R l t
  rw [e1, abs_mul, abs_inv, abs_of_pos hB]
  rw [div_le_iff₀ ha] at h
  rw [div_le_iff₀ ha]
  calc 1 = B⁻¹ * B := by field_simp
    _ ≤ B⁻¹ * (|eval (gx l t) (pderiv 3 R)| * a) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = B⁻¹ * |eval (gx l t) (pderiv 3 R)| * a := by ring

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
