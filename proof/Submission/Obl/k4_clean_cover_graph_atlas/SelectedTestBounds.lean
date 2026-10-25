import Submission.Obl.k4_clean_cover_graph_atlas.InitialScale
import Submission.Obl.k4_quadratic_atlas_normalization.Curvature

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MvPolynomial Submission.Lib.K4QuadraticSheets

/-- Original quadratic coefficient bounds control its constant hidden curvature. -/
theorem quadratic_qc_coeff_bound (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {H : ℝ} (hH : 0 ≤ H) (hcoeff : ∀ d, |P.coeff d| ≤ H) : |qc P| ≤ 4 * H := by
  have h1 := Submission.Obl.k4_quadratic_atlas_normalization.quadratic_pderiv_coeff_bound
    P hP (3 : Fin 4) hH hcoeff
  have hPd : (pderiv (3 : Fin 4) P).totalDegree ≤ 2 := (totalDegree_pderiv_le' P _ hP).trans (by norm_num)
  have h2 := Submission.Obl.k4_quadratic_atlas_normalization.quadratic_pderiv_coeff_bound
    (pderiv (3 : Fin 4) P) hPd (3 : Fin 4) (by positivity : 0 ≤ 2 * H) h1 (0 : Fin 4 →₀ ℕ)
  simpa only [qc, last_three, eval_zero, constantCoeff_eq, show 2 * (2 * H) = 4 * H by ring] using h2

/-- Both selected physical tests retain degree two and uniformly bounded
coefficients, first derivative coefficients and constant hidden curvature. -/
theorem selectedSheetTest_original_bounds (flat : Bool) (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) {H : ℝ} (hH : 0 ≤ H) (hcoeff : ∀ d, |P.coeff d| ≤ H) :
    (selectedSheetTest flat P).totalDegree ≤ 2 ∧
    (∀ d, |(selectedSheetTest flat P).coeff d| ≤ 2 * H ∧
      |(pderiv (3 : Fin 4) (selectedSheetTest flat P)).coeff d| ≤ 4 * H) ∧
    |qc (selectedSheetTest flat P)| ≤ 8 * H := by
  have hdeg : (selectedSheetTest flat P).totalDegree ≤ 2 := by
    cases flat
    · exact hP
    · exact (totalDegree_pderiv_le' P (3 : Fin 4) hP).trans (by norm_num)
  have hcoef : ∀ d, |(selectedSheetTest flat P).coeff d| ≤ 2 * H := by
    cases flat
    · exact fun d => (hcoeff d).trans (by linarith)
    · exact Submission.Obl.k4_quadratic_atlas_normalization.quadratic_pderiv_coeff_bound
        P hP (3 : Fin 4) hH hcoeff
  have hder := Submission.Obl.k4_quadratic_atlas_normalization.quadratic_pderiv_coeff_bound
    _ hdeg (3 : Fin 4) (by positivity : 0 ≤ 2 * H) hcoef
  refine ⟨hdeg, fun d => ⟨hcoef d, by simpa only [show 2 * (2 * H) = 4 * H by ring] using hder d⟩, ?_⟩
  simpa only [show 4 * (2 * H) = 8 * H by ring] using
    quadratic_qc_coeff_bound _ hdeg (by positivity : 0 ≤ 2 * H) hcoef

/-- The normalized curvature in the physical scale bound cancels both hidden
normalization factors. Thus the selected scale costs no inverse fine thickness. -/
theorem physical_initial_scale_upper {T j : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {B A sc H : ℝ} {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) (hB : 0 < B) (hH : 0 ≤ H) (hcoeff : ∀ d, |P.coeff d| ≤ H)
    (hsc : sc ≤ B * A + B ^ 2 * |qc (normPoly T j c u Q B P)|) :
    sc ≤ B * A + 4 * H := by
  have he : B ^ 2 * |qc (normPoly T j c u Q B P)| = |qc P| := by
    rw [qc_normPoly hP, abs_mul, abs_mul, abs_inv, abs_of_pos hB]
    field_simp
  rw [he] at hsc
  exact hsc.trans (add_le_add le_rfl (quadratic_qc_coeff_bound P hP hH hcoeff))

end Submission.Obl.k4_clean_cover_graph_atlas
