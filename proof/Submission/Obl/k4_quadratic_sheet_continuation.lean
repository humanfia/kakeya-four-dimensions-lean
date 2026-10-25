import Mathlib
import ChallengeDeps
import Submission.Obl.k4_quadratic_sheet_continuation.Scalar
import Submission.Obl.k4_quadratic_sheet_continuation.ScalarReduction
set_option linter.unusedVariables false

/-!
# `Submission.k4_quadratic_sheet_continuation`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_quadratic_sheet_continuation`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_quadratic_sheet_continuation/`
belong to this obligation.
-/

theorem Submission.k4_quadratic_sheet_continuation : ∀ n m D s : ℕ, ∃ q : ℕ, ∃ C : ℝ, s ≤ q ∧ 0 < C ∧ ∀ A : ℝ, 2 ≤ A → ∀ a b c : EuclideanSpace ℂ (Fin n), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ (P : Fin m → MvPolynomial (Fin (n + 1)) ℂ) (f : Fin m → EuclideanSpace ℂ (Fin n) → ℂ) (Q : MvPolynomial (Fin (n + m)) ℂ), (fun U : Set (EuclideanSpace ℂ (Fin n)) => (fun H : EuclideanSpace ℂ (Fin n) → ℂ => (∀ i, P i ≠ 0 ∧ (P i).totalDegree ≤ 2 ∧ DifferentiableOn ℂ (f i) U ∧ ∀ z ∈ U, MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f i z)) (P i) = 0 ∧ MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f i z)) (MvPolynomial.pderiv (Fin.last n) (P i)) ≠ 0) → Q.totalDegree ≤ D → ∀ V : ℝ, 0 ≤ V → ((∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ V) → (∀ z ∈ Metric.closedBall c ((8 * A)⁻¹), ‖H z‖ ≤ A ^ C * V) ∧ ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ A ^ C * V) ∧ ((∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ V) → ∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ A ^ C * V)) (fun z => MvPolynomial.eval (Fin.append (fun j : Fin n => z j) (fun i : Fin m => f i z)) Q)) (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) :=
  Submission.Obl.k4_quadratic_sheet_continuation.quadratic_sheet_continuation_of_scalar
    Submission.Obl.k4_quadratic_sheet_continuation.scalar_jet_propagation
