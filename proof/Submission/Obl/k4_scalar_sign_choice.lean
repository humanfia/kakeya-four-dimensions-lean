import Mathlib
import ChallengeDeps
import Submission.Obl.k4_sign_projection
import Submission.Obl.k4_scalar_sign_choice.ScalarChoice
set_option linter.unusedVariables false

/-!
# `Submission.k4_scalar_sign_choice`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_scalar_sign_choice`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_scalar_sign_choice/`
belong to this obligation.
-/

theorem Submission.k4_scalar_sign_choice : ∀ (ι η : Type) [Fintype ι] [Fintype η] (p : η → MvPolynomial (ι ⊕ Unit) ℝ) (B : Set (η → SignType)), ∃ (b : (ι → ℝ) → ℝ) (n : ℕ) (g : Fin n → MvPolynomial (ι ⊕ Unit) ℝ) (A : Set (Fin n → SignType)), (∀ (x : ι → ℝ) (t : ℝ), (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x (fun _ : Unit => t)) (g i))) ∈ A ↔ (∃ u : ℝ, (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x (fun _ : Unit => u)) (p i))) ∈ B) ∧ b x = t) ∧ (∀ x : ι → ℝ, (∃ u : ℝ, (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x (fun _ : Unit => u)) (p i))) ∈ B) → (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x (fun _ : Unit => b x)) (p i))) ∈ B) := by
  exact Submission.Obl.k4_scalar_sign_choice.scalar_choice_of_projection
    (Submission.Obl.k4_scalar_sign_choice.signProjection_of_family_projection
      Submission.k4_sign_projection)
