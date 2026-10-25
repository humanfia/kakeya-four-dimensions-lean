import Mathlib
import ChallengeDeps
import Submission.Obl.k4_adapted_oscillation_tests.Glue
set_option linter.unusedVariables false

/-!
# `Submission.k4_adapted_oscillation_tests`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_adapted_oscillation_tests`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_adapted_oscillation_tests/`
belong to this obligation.
-/

theorem Submission.k4_adapted_oscillation_tests : ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ V : Seminorm ℝ (EuclideanSpace ℝ (Fin n)), Continuous V → (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ V v) → ∀ c : EuclideanSpace ℝ (Fin n), ∃ (k : ℕ) (Q : Fin k → Set (EuclideanSpace ℝ (Fin n))), (k : ℝ) ≤ C * (MeasureTheory.volume {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1}).toReal⁻¹ ∧ (∀ h : Fin k, IsCompact (Q h) ∧ 0 < MeasureTheory.volume (Q h) ∧ Q h ⊆ Metric.ball c 1) ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f → (∀ h : Fin k, |MeasureTheory.integral (MeasureTheory.volume.restrict (Q h)) f| ≤ (MeasureTheory.volume (Q h)).toReal / 2 ∧ (MeasureTheory.volume (Q h)).toReal ≤ MeasureTheory.integral (MeasureTheory.volume.restrict (Q h)) (fun x => |f x|)) → ∃ v : EuclideanSpace ℝ (Fin n), V v ≤ 1 ∧ A ≤ MeasureTheory.integral (MeasureTheory.volume.restrict (Metric.ball c 1)) (fun x : EuclideanSpace ℝ (Fin n) => ‖(fderiv ℝ f x) v‖) := by
  intro n hn A hA
  exact Submission.Obl.k4_adapted_oscillation_tests.main n hn A hA
