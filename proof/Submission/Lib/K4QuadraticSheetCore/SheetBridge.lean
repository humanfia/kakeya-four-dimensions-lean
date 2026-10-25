import Mathlib
import Submission.Lib.K4ContactNormalization
import Submission.Lib.K4QuadraticSheetCore.SheetAffine

/-! Adapted from: here:o223 (session x0777, branch x0777). -/

/-!
# Bridge from four-variable tests to the base data of the affine-sheet core

A test `G : MvPolynomial (Fin 4) ℝ` of total degree at most two, with the hidden variable last,
is `γ + β w + α w²` with `γ = G(·, 0)`, `β = ∂_w G(·, 0)` and `α = ∂_w² G / 2`. Along a line
`point b σ = (σ, b0 + σ b3, b1 + σ b4, b2 + σ b5)` the test and its hidden derivative are exactly
`testVal α β γ b σ` and `testDer α β b σ`, so the hypotheses of `sff_frame_bound` and of
`line_near_affine_branches` can be read off the frozen fit predicate after normalization.
-/

namespace Submission.Lib.K4QuadraticSheetCore

open MvPolynomial Set
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting (eval_bind₁')

noncomputable section

/-- Substitute zero for the hidden variable and keep the three base variables. -/
def baseRestrict (P : MvPolynomial (Fin 4) ℝ) : BasePoly :=
  bind₁ (fun i : Fin 4 => if h : (i : ℕ) < 3 then X (⟨i, h⟩ : Fin 3) else 0) P

/-- The base point with zero hidden coordinate. -/
def withZeroHidden (p : Fin 3 → ℝ) : Fin 4 → ℝ := ![p 0, p 1, p 2, 0]

theorem eval_baseRestrict (P : MvPolynomial (Fin 4) ℝ) (p : Fin 3 → ℝ) :
    eval p (baseRestrict P) = eval (withZeroHidden p) P := by
  unfold baseRestrict
  rw [eval_bind₁']
  have h : (fun i : Fin 4 => eval p (if h : (i : ℕ) < 3 then X (⟨i, h⟩ : Fin 3) else 0)) =
      withZeroHidden p := by
    funext i
    fin_cases i <;> simp [withZeroHidden]
  rw [h]

theorem baseRestrict_degree (P : MvPolynomial (Fin 4) ℝ) :
    (baseRestrict P).totalDegree ≤ P.totalDegree := by
  unfold baseRestrict
  apply Submission.Lib.K4ChartLifting.totalDegree_bind₁_le_of_le_one
  intro i
  fin_cases i <;> simp

/-- The base data of a four-variable test. -/
def testGamma (G : MvPolynomial (Fin 4) ℝ) : BasePoly := baseRestrict G
def testBeta (G : MvPolynomial (Fin 4) ℝ) : BasePoly := baseRestrict (pderiv 3 G)
def testAlpha (G : MvPolynomial (Fin 4) ℝ) : ℝ := eval (fun _ => (0 : ℝ)) (pderiv 3 (pderiv 3 G)) / 2

theorem testGamma_degree (G : MvPolynomial (Fin 4) ℝ) (hG : G.totalDegree ≤ 2) :
    (testGamma G).totalDegree ≤ 2 := (baseRestrict_degree G).trans hG

theorem testBeta_degree (G : MvPolynomial (Fin 4) ℝ) (hG : G.totalDegree ≤ 2) :
    (testBeta G).totalDegree ≤ 1 :=
  (baseRestrict_degree _).trans
    ((Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred G 3).trans (by omega))

theorem point_eq_update (b : Fin 6 → ℝ) (σ : ℝ) :
    point b σ = Function.update (withZeroHidden (lineP b σ)) 3
      (withZeroHidden (lineP b σ) 3 + lineW b σ) := by
  funext i
  fin_cases i <;> simp [point, withZeroHidden, lineP, lineW, Function.update]

/-- The test along a line is the base test of the core. -/
theorem eval_point_eq_testVal (G : MvPolynomial (Fin 4) ℝ) (hG : G.totalDegree ≤ 2)
    (b : Fin 6 → ℝ) (σ : ℝ) :
    eval (point b σ) G = testVal (testAlpha G) (testBeta G) (testGamma G) b σ := by
  rw [point_eq_update, Submission.Lib.K4HiddenQuadratic.eval_update_add G hG]
  have hc := Submission.Lib.K4HiddenQuadratic.eval_pderiv_pderiv_eq G hG 3
    (withZeroHidden (lineP b σ)) (fun _ => 0)
  simp only [testVal, testAlpha, testBeta, testGamma, eval_baseRestrict, hc]
  ring

/-- The hidden derivative along a line is the core's hidden derivative. -/
theorem eval_point_pderiv_eq_testDer (G : MvPolynomial (Fin 4) ℝ) (hG : G.totalDegree ≤ 2)
    (b : Fin 6 → ℝ) (σ : ℝ) :
    eval (point b σ) (pderiv 3 G) = testDer (testAlpha G) (testBeta G) b σ := by
  rw [point_eq_update, Submission.Lib.K4HiddenQuadratic.eval_update_add_pderiv G hG]
  have hc := Submission.Lib.K4HiddenQuadratic.eval_pderiv_pderiv_eq G hG 3
    (withZeroHidden (lineP b σ)) (fun _ => 0)
  simp only [testDer, testAlpha, testBeta, eval_baseRestrict, hc]
  ring

/-- The curvature of a four-variable test. -/
theorem abs_two_testAlpha (G : MvPolynomial (Fin 4) ℝ) (hG : G.totalDegree ≤ 2)
    (x : Fin 4 → ℝ) :
    |2 * testAlpha G| = |eval x (pderiv 3 (pderiv 3 G))| := by
  have hc := Submission.Lib.K4HiddenQuadratic.eval_pderiv_pderiv_eq G hG 3 x (fun _ => 0)
  rw [testAlpha, hc]
  ring_nf

end

end Submission.Lib.K4QuadraticSheetCore
