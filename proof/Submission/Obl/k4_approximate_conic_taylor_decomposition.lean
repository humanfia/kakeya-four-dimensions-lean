import Mathlib
import ChallengeDeps
import Submission.Obl.k4_approximate_conic_taylor_decomposition.BackupProof
set_option linter.unusedVariables false

/-!
# `Submission.k4_approximate_conic_taylor_decomposition`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_approximate_conic_taylor_decomposition`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_approximate_conic_taylor_decomposition/`
belong to this obligation.
-/

theorem Submission.k4_approximate_conic_taylor_decomposition : ∃ K : ℕ, 6 ≤ K ∧ ∀ (A ε h : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (R : (EuclideanSpace ℝ (Fin 3)) → ℝ) (p : Fin 7 → (EuclideanSpace ℝ (Fin 3))), 2 ≤ A → 0 < ε → ε ≤ 1 → 0 < h → h * A ^ K ≤ ε → M.IsSymm → (A ^ 4)⁻¹ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |M i j| → (∑ i : Fin 3, ∑ j : Fin 3, |M i j|) ≤ A ^ 4 → (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) → (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) → (∀ i : Fin 7, |(fun u : (EuclideanSpace ℝ (Fin 3)) => ∑ i : Fin 3, ∑ j : Fin 3, u i * M i j * u j) (p i)| ≤ A * h) → ContDiffOn ℝ 6 R (Metric.ball (0 : (EuclideanSpace ℝ (Fin 3))) 3) → (∀ j : ℕ, j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j R u‖ ≤ A) → (∀ i : Fin 7, ∀ j : ℕ, j ≤ 2 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j (fun v : (EuclideanSpace ℝ (Fin 3)) => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u‖ ≤ A * ε) → ∃ (L : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ) (lam : ℝ), ‖L‖ ≤ A ^ K ∧ |lam| ≤ A ^ K ∧ ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1, |R u - (R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2 + (fun u : (EuclideanSpace ℝ (Fin 3)) => ∑ i : Fin 3, ∑ j : Fin 3, u i * M i j * u j) u * L u + lam * ((fun u : (EuclideanSpace ℝ (Fin 3)) => ∑ i : Fin 3, ∑ j : Fin 3, u i * M i j * u j) u) ^ 2)| ≤ A ^ K * ε := by
  exact Submission.Obl.k4_approximate_conic_taylor_decomposition.Backup.decomposition
