import Mathlib
import ChallengeDeps
import Submission.Obl.k4_bounded_sign_choice.CoordinateChoice
set_option linter.unusedVariables false

/-!
# `Submission.k4_bounded_sign_choice`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_bounded_sign_choice`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_bounded_sign_choice/`
belong to this obligation.
-/

theorem Submission.k4_bounded_sign_choice : ∀ m d : ℕ, ∃ C : ℕ, 0 < C ∧ ∀ (p : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ) (B : Set (Fin m → SignType)), (∀ i, (p i).totalDegree ≤ d) → ∃ (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (g : Fin C → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ) (A : Set (Fin C → SignType)), (∀ i, (g i).totalDegree ≤ C) ∧ (∀ s y : EuclideanSpace ℝ (Fin 3), (fun i => SignType.sign (MvPolynomial.eval (Sum.elim (fun k : Fin 3 => s k) (fun k : Fin 3 => y k)) (g i))) ∈ A ↔ (∃ y : EuclideanSpace ℝ (Fin 3), (fun i => SignType.sign (MvPolynomial.eval (Sum.elim (fun k : Fin 3 => s k) (fun k : Fin 3 => y k)) (p i))) ∈ B) ∧ b s = y) ∧ (∀ s : EuclideanSpace ℝ (Fin 3), (∃ y : EuclideanSpace ℝ (Fin 3), (fun i => SignType.sign (MvPolynomial.eval (Sum.elim (fun k : Fin 3 => s k) (fun k : Fin 3 => y k)) (p i))) ∈ B) → (fun i => SignType.sign (MvPolynomial.eval (Sum.elim (fun k : Fin 3 => s k) (fun k : Fin 3 => (b s) k)) (p i))) ∈ B) := by
  exact Submission.Obl.k4_bounded_sign_choice.bounded_sign_choice_of_qualitative
    Submission.Obl.k4_bounded_sign_choice.Coordinates.qualitativeChoice_of_projection_scalar
