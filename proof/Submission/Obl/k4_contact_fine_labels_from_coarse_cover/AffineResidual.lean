-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/AffineResidual.lean
import Submission.Lib.K4ContactNormalization.HomogeneousCorrection
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting
open Submission.Obl.k4_quadratic_atlas_normalization
open Submission.Obl.k4_stable_native_signal_oscillation

/-- Translate only the hidden coordinate by an arbitrary affine predictor.
No coefficient bound on the predictor is included in this definition. -/
noncomputable def translatedTest (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ) :
    MvPolynomial (Fin 4) ℝ := residualLift (fun i => -L i) 1 F

theorem translatedTest_degree (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ) :
    (translatedTest L F).totalDegree ≤ F.totalDegree := residualLift_degree _ _ _

theorem pderiv_translatedTest (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (translatedTest L F) = translatedTest L (pderiv 3 F) := by
  unfold translatedTest
  rw [pderiv_residualLift _ one_ne_zero]
  simp only [residualLift, C_1, one_mul]

theorem curvature_translatedTest (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ)
    (hF : F.totalDegree ≤ 2) : curvature (translatedTest L F) 3 = curvature F 3 := by
  change (pderiv 3 (pderiv 3 (translatedTest L F))).coeff 0 = curvature F 3
  rw [pderiv_translatedTest, pderiv_translatedTest, second_pderiv_eq_curvature F hF 3]
  simp [translatedTest, residualLift]

theorem residualCoeff_inverse (L : Fin 4 → ℝ) (b : Fin 6 → ℝ) :
    residualCoeff (fun i => -L i) 1 (residualCoeff L 1 b) = b := by
  funext i
  fin_cases i <;> simp [residualCoeff] <;> ring

theorem point_residualCoeff_one (L : Fin 4 → ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    point (residualCoeff L 1 b) t = Fin.snoc (Fin.init (point b t))
      (point b t 3 - eval (point b t) (affineBase L)) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change point (residualCoeff L 1 b) t (Fin.last 3) =
      point b t 3 - eval (point b t) (affineBase L)
    simp [point, residualCoeff, affineBase]
    ring

/-- The translated equation tests exactly the original trajectory when
applied to its original affine residual. -/
theorem eval_translatedTest_residual (L : Fin 4 → ℝ)
    (F : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point (residualCoeff L 1 b) t) (translatedTest L F) = eval (point b t) F := by
  rw [translatedTest, eval_residualLift, one_mul, residualCoeff_inverse]

theorem eval_pderiv_translatedTest_residual (L : Fin 4 → ℝ)
    (F : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point (residualCoeff L 1 b) t) (pderiv 3 (translatedTest L F)) =
      eval (point b t) (pderiv 3 F) := by
  rw [pderiv_translatedTest, eval_translatedTest_residual]

theorem restrictBase_translatedTest (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ) :
    restrictBase (translatedTest L F) = affineSheetRestriction L F := by
  apply MvPolynomial.funext
  intro z
  rw [eval_restrictBase]
  have h := eval_affineSheetRestriction L F (Fin.snoc z 0)
  have hbase : (Fin.snoc z (0 : ℝ) : Fin 4 → ℝ) ∘ Fin.castSucc = z := by
    funext i
    simp only [Function.comp_def, Fin.snoc_castSucc]
  rw [hbase] at h
  rw [h]
  unfold translatedTest residualLift
  rw [eval_mul, eval_C, one_mul, eval_bind₁']
  apply congrArg (fun v : Fin 4 → ℝ => eval v F)
  have hzlast : (Fin.snoc z (0 : ℝ) : Fin 4 → ℝ) 3 = 0 := by
    rw [show (3 : Fin 4) = Fin.last 3 by decide, Fin.snoc_last]
  funext i
  induction i using Fin.lastCases with
  | last =>
      simp only [show (Fin.last 3 : Fin 4) = 3 by decide, residualSubst,
        Matrix.cons_val, Fin.reduceFinMk, eval_mul, eval_C, inv_one, one_mul,
        map_sub, eval_X, Function.update_self, hzlast]
      simp only [affineBase, map_add, eval_mul, eval_C, eval_X]
      ring
  | cast j =>
      have hj : (j.castSucc : Fin 4) ≠ 3 := by fin_cases j <;> decide
      rw [Function.update_of_ne hj]
      fin_cases j
      · change eval (Fin.snoc z (0 : ℝ)) (X (0 : Fin 4)) = (Fin.snoc z (0 : ℝ) : Fin 4 → ℝ) 0
        exact eval_X _
      · change eval (Fin.snoc z (0 : ℝ)) (X (1 : Fin 4)) = (Fin.snoc z (0 : ℝ) : Fin 4 → ℝ) 1
        exact eval_X _
      · change eval (Fin.snoc z (0 : ℝ)) (X (2 : Fin 4)) = (Fin.snoc z (0 : ℝ) : Fin 4 → ℝ) 2
        exact eval_X _

theorem restrictBase_pderiv_translatedTest (L : Fin 4 → ℝ)
    (F : MvPolynomial (Fin 4) ℝ) :
    restrictBase (pderiv 3 (translatedTest L F)) = affineSheetRestriction L (pderiv 3 F) := by
  rw [pderiv_translatedTest, restrictBase_translatedTest]

/-- Observed derivative and curvature bounds control the shifted base
polynomials, without any bound on the affine coefficients. -/
theorem affine_shift_base_value_bounds (L : Fin 4 → ℝ)
    (F : MvPolynomial (Fin 4) ℝ) (hF : F.totalDegree ≤ 2) (v : Fin 4 → ℝ)
    {K a H : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (hH : 0 ≤ H)
    (hval : |eval v F| ≤ K * a) (hfirst : |eval v (pderiv 3 F)| ≤ K)
    (hsecond : |eval v (pderiv 3 (pderiv 3 F))| ≤ K / a)
    (hclose : |eval v (affineBase L) - v 3| ≤ H) :
    |eval (Fin.init v) (restrictBase (translatedTest L F))| ≤
        K * a + H * K + H ^ 2 / 2 * (K / a) ∧
      |eval (Fin.init v) (restrictBase (pderiv 3 (translatedTest L F)))| ≤
        K + (K / a) * H := by
  have hcurv : |curvature F 3| ≤ K / a := by
    rwa [second_pderiv_eq_curvature F hF 3, eval_C] at hsecond
  have hbase : Fin.init v = v ∘ Fin.castSucc := rfl
  rw [restrictBase_translatedTest, restrictBase_pderiv_translatedTest, hbase]
  constructor
  · have h := affine_correction_error L F hF v hH hclose hfirst hsecond
    rw [eval_baseCalibratedTest] at h
    have ht := abs_sub_le (eval (v ∘ Fin.castSucc) (affineSheetRestriction L F))
      (eval v F) 0
    have ht' : |eval (v ∘ Fin.castSucc) (affineSheetRestriction L F)| ≤
        |eval v F - eval (v ∘ Fin.castSucc) (affineSheetRestriction L F)| + |eval v F| := by
      simpa only [sub_zero, abs_sub_comm] using ht
    exact ht'.trans ((add_le_add h hval).trans_eq (by ring))
  · rw [eval_affineSheetRestriction]
    have h := quadratic_coordinate_derivative F hF v (3 : Fin 4)
      (eval v (affineBase L) - v 3)
    rw [show v 3 + (eval v (affineBase L) - v 3) = eval v (affineBase L) by ring] at h
    rw [h]
    exact (abs_add_le _ _).trans (by
      rw [abs_mul]
      exact add_le_add hfirst (mul_le_mul hcurv hclose (abs_nonneg _) (div_nonneg hK ha.le)))

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
