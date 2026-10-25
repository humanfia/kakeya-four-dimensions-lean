/- Adapted from: here:o267
   Session x0945, commit 0ec669f1, Submission/Obl/k4_original_potential_reference_completion/PotentialThirdJets.lean.
   General library export; earlier provenance comments are retained below. -/
import Submission.Lib.K4PotentialPlaneMenus.Basic
import Submission.Lib.K4CubicTests.PolynomialTaylor

namespace Submission.Lib.K4PotentialPlaneMenus.PotentialThirdJets

open MvPolynomial Set
open Submission.Lib.K4CubicTests

noncomputable section

/-- Iteration of the accepted formal directional derivative computes all
actual derivatives along an affine row. -/
theorem iteratedDeriv_eval_affine {ι : Type*} [Fintype ι]
    (P : MvPolynomial ι ℝ) (c v : ι → ℝ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun s => eval (fun i => c i + s * v i) P) t =
      eval (fun i => c i + t * v i) ((polynomialDirectionalDerivative v)^[n] P) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv n (fun s => eval (fun i => c i + s * v i) P) =
      (fun s => eval (fun i => c i + s * v i)
        ((polynomialDirectionalDerivative v)^[n] P)) from _root_.funext ih]
    rw [Function.iterate_succ_apply']
    exact (hasDerivAt_eval_polynomial_line _ c v t).deriv

def timeOneSubstitution : Fin 3 → MvPolynomial (Fin 2) ℝ := ![1, X 0, X 1]

end

end Submission.Lib.K4PotentialPlaneMenus.PotentialThirdJets
