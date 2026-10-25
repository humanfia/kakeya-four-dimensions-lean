-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/ParentFrame.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
-- Adapted from this LOT tree, o199, session x0700, commit 711b90f1.
-- Source: Submission/Obl/k4_finite_path_candidate_conversion/ParentFrame.lean.
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.Normalize
import Submission.Obl.k4_finite_affine_candidate_return.EStages
import Submission.Lib.K4XInterface

/-!
# Normalising through a parent chart, with a rescaled hidden coordinate

The model of o199 works in the coordinates of one parent chart: time `τ = (t - t₀)/q`, spatial
`z = D⁻¹ (y - c - t u)` (accepted o184's `Normalization.Frame`), and the hidden coordinate rescaled
to `W = sc · w`, so that the parent's derivative unit becomes one (`sc = B / δ`). `PFrame.eb` are the
normalised line coefficients; `PFrame.liftE` pulls a model test back to the original coordinates and
`PFrame.normTest` pushes an original test forward, with exact evaluation, hidden-derivative and degree
rules. Written by x0700 for o199 (builds on o184's `Frame`).
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_affine_candidate_return

open MvPolynomial Submission.Lib.K4XInterface
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

/-- A parent frame: o184's normalising frame and a hidden scale. -/
structure PFrame where
  F : Frame
  sc : ℝ

namespace PFrame

variable (Φ : PFrame)

/-- The normalised coefficients of a line, hidden coordinate rescaled by `sc`. -/
def eb (l : ℕ × (Fin 6 → ℝ)) : Fin 6 → ℝ :=
  ![Φ.F.normCoeff l.2 0, Φ.F.normCoeff l.2 1, Φ.sc * Φ.F.normCoeff l.2 2,
    Φ.F.normCoeff l.2 3, Φ.F.normCoeff l.2 4, Φ.sc * Φ.F.normCoeff l.2 5]

/-- The substitution from original to model graph coordinates. -/
def subst' : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![Φ.F.subst 0, Φ.F.subst 1, Φ.F.subst 2, C Φ.sc * X 3]

theorem graphPoint_eq_gx (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : graphPoint l t = gx l t := rfl

theorem eval_subst' (hq : Φ.F.q ≠ 0) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    (fun i => eval (gx l t) (Φ.subst' i)) = exS Φ.eb l ((t - Φ.F.t₀) / Φ.F.q) := by
  have h := Φ.F.eval_subst hq l t
  rw [← graphPoint_eq_gx]
  funext i
  have hi := congrFun h i
  fin_cases i
  · simpa [subst', exS, eb, Frame.normTraj, graphPoint] using hi
  · simpa [subst', exS, eb, Frame.normTraj, graphPoint] using hi
  · simpa [subst', exS, eb, Frame.normTraj, graphPoint] using hi
  · have h3 : (graphPoint l t) 3 = Φ.F.normCoeff l.2 2 +
        (t - Φ.F.t₀) / Φ.F.q * Φ.F.normCoeff l.2 5 := by
      simpa [Frame.normTraj, Frame.subst, graphPoint] using hi
    show eval (graphPoint l t) (C Φ.sc * X 3) =
      Φ.sc * Φ.F.normCoeff l.2 2 + (t - Φ.F.t₀) / Φ.F.q * (Φ.sc * Φ.F.normCoeff l.2 5)
    rw [eval_mul, eval_C, eval_X, h3]
    ring

theorem totalDegree_subst'_le (i : Fin 4) : (Φ.subst' i).totalDegree ≤ 1 := by
  fin_cases i
  · exact Φ.F.totalDegree_subst_le 0
  · exact Φ.F.totalDegree_subst_le 1
  · exact Φ.F.totalDegree_subst_le 2
  · exact deg1_C_mul _ (deg1_X _)

/-- A model test pulled back to original coordinates, times `δ`. -/
def liftE (δ : ℝ) (Q : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  δ • bind₁ Φ.subst' Q

theorem eval_liftE (hq : Φ.F.q ≠ 0) (δ : ℝ) (Q : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    eval (gx l t) (Φ.liftE δ Q) = δ * eval (exS Φ.eb l ((t - Φ.F.t₀) / Φ.F.q)) Q := by
  rw [liftE, smul_eval, ← Φ.eval_subst' hq l t, eval_bind₁']

theorem totalDegree_liftE_le (δ : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    (Φ.liftE δ Q).totalDegree ≤ Q.totalDegree :=
  (totalDegree_smul_le _ _).trans (totalDegree_bind₁_le_of_le_one _ Φ.totalDegree_subst'_le Q)

theorem pderiv_three_subst' (j : Fin 4) :
    pderiv (3 : Fin 4) (Φ.subst' j) = if j = 3 then C Φ.sc else 0 := by
  fin_cases j
  · simp [subst', Φ.F.pderiv_three_subst_of_ne 0 (by decide)]
  · simp [subst', Φ.F.pderiv_three_subst_of_ne 1 (by decide)]
  · simp [subst', Φ.F.pderiv_three_subst_of_ne 2 (by decide)]
  · simp [subst', pderiv_X]

theorem pderiv_liftE (δ : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (Φ.liftE δ Q) = Φ.sc • Φ.liftE δ (pderiv 3 Q) := by
  rw [liftE, liftE, Derivation.map_smul, pderiv_bind₁, Fin.sum_univ_four]
  simp only [Φ.pderiv_three_subst', Fin.isValue, Fin.reduceEq, ite_false, ite_true, mul_zero,
    zero_add]
  simp only [smul_eq_C_mul]
  ring

/-- The substitution from model to original graph coordinates. -/
def isubst : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C Φ.F.t₀ + C Φ.F.q * X 0,
    C (Φ.F.c 0) + (C Φ.F.t₀ + C Φ.F.q * X 0) * C (Φ.F.u 0) + C (Φ.F.D 0 0) * X 1 +
      C (Φ.F.D 0 1) * X 2,
    C (Φ.F.c 1) + (C Φ.F.t₀ + C Φ.F.q * X 0) * C (Φ.F.u 1) + C (Φ.F.D 1 0) * X 1 +
      C (Φ.F.D 1 1) * X 2,
    C Φ.sc⁻¹ * X 3]

end PFrame

end

end Submission.Obl.k4_finite_affine_candidate_return
