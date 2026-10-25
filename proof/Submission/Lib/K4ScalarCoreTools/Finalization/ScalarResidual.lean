/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/ScalarResidual.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Residual polynomial, degree and evaluation: accepted here:o177, ScalarFormat.lean (o120/x0402,81f800489248f55eaf1c2da13f86ceff0ee98719).
Scalar trajectory definitions: same source ScalarCandidates.lean. Degree facts are imported from accepted K4ScalarSwitching.
-/

import Submission.Lib.K4ScalarSwitching.SwitchPath
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open MvPolynomial
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

noncomputable def scalarY (b : Fin 5 → ℝ) (t : ℝ) : ℝ := b 0 + t * b 1

noncomputable def scalarX (b : Fin 5 → ℝ) (t : ℝ) : ℝ := b 2 + t * b 3 + t ^ 2 * b 4

noncomputable def scalarErrorPolynomial (P : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    MvPolynomial (Fin 5) ℝ :=
  X 2 + C t * X 3 + C (t ^ 2) * X 4 -
    aeval ![C t, X 0 + C t * X 1] P

theorem scalarErrorPolynomial_degree (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t : ℝ) :
    (scalarErrorPolynomial P t).totalDegree ≤ 2 := by
  apply degree_sub_le
  · apply degree_add_le
    · exact degree_add_le (by simp) ((degree_C_mul_le _ _).trans (by simp))
    · exact (degree_C_mul_le _ _).trans (by simp)
  · apply (degree_aeval_le _ _ ?_).trans hP
    intro i
    fin_cases i
    · change (C t : MvPolynomial (Fin 5) ℝ).totalDegree ≤ 1
      simp
    · apply degree_add_le (by simp) ((degree_C_mul_le _ _).trans (by simp))

theorem eval_scalarErrorPolynomial (P : MvPolynomial (Fin 2) ℝ)
    (t : ℝ) (b : Fin 5 → ℝ) :
    eval b (scalarErrorPolynomial P t) = scalarX b t - eval ![t, scalarY b t] P := by
  simp only [scalarErrorPolynomial, map_sub, map_add, map_mul, eval_X, eval_C,
    Submission.Lib.K4ScalarSwitching.Switching.eval_substitution]
  have hv : (fun i => eval b (![C t, X 0 + C t * X 1] i)) =
      (![t, scalarY b t] : Fin 2 → ℝ) := by
    ext i
    fin_cases i <;> simp [scalarY]
  rw [hv]
  simp only [scalarX]

end Submission.Lib.K4ScalarCoreTools.Finalization
