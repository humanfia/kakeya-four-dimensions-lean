import Mathlib
import ChallengeDeps
import Submission.Obl.k4_algebraic_sheet_bound.Uniform
set_option linter.unusedVariables false

/-!
# `Submission.k4_algebraic_sheet_bound`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_algebraic_sheet_bound`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_algebraic_sheet_bound/`
belong to this obligation.
-/

theorem Submission.k4_algebraic_sheet_bound : ∀ n D : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin (n + 1)) ℂ) (f : EuclideanSpace ℂ (Fin n) → ℂ), P ≠ 0 → P.totalDegree ≤ D → DifferentiableOn ℂ f (Metric.ball 0 4) → (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 4, MvPolynomial.eval (Fin.snoc (fun i : Fin n => z i) (f z)) P = 0) → (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 → ‖f (WithLp.toLp 2 (fun i : Fin n => (x i : ℂ)))‖ ≤ 1) → ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ 1 → ‖f z‖ ≤ C := by
  intro n D
  obtain ⟨C, hC, hbound⟩ :=
    Submission.Obl.k4_algebraic_sheet_bound.uniform_basis_sheet_bound n D
  refine ⟨C, hC, ?_⟩
  intro P f hP hdeg hdiff hroot hbase z hz
  obtain ⟨c, hc, a, ha, heval⟩ :=
    Submission.Obl.k4_algebraic_sheet_bound.exists_unit_polyOf hP hdeg
  apply hbound c f hc hdiff _ hbase z hz
  intro v hv
  rw [heval, hroot v hv, mul_zero]
