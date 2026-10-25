import Submission.Obl.k4_stable_native_signal_oscillation.PolynomialControlCore
import Submission.Obl.k4_stable_native_signal_oscillation.PolynomialRemez

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial Set Metric MeasureTheory

/-- Fixed-degree polynomials bounded on a base set of reciprocal-polynomial volume
have polynomial bounds and Lipschitz constants on the threefold enlarged ball. -/
lemma exists_polynomial_control (D m : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ K : ℝ, 2 ≤ K →
      ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ (E : Set (EuclideanSpace ℝ (Fin 3))) (V : ℝ), 0 ≤ V →
      E ⊆ closedBall 0 K → ENNReal.ofReal ((K ^ m)⁻¹) ≤ volume E →
      (∀ x ∈ E, |eval (fun i => x i) P| ≤ V) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K → |eval (fun i => x i) P| ≤ K ^ N * V) ∧
      ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K → ‖y‖ ≤ 3 * K →
        |eval (fun i => x i) P - eval (fun i => y i) P| ≤ K ^ N * V * ‖x - y‖ := by
  obtain ⟨C, hC, hremez⟩ := exists_polynomial_remez_half_ball D
  exact polynomial_control_of_remez D m C hC hremez

/-- The precise quadratic center estimate used in the native-signal argument. -/
lemma exists_center_polynomial_lipschitz :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ K : ℝ, 2 ≤ K →
      ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ 2 →
      ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
      E ⊆ closedBall 0 K → ENNReal.ofReal K⁻¹ ≤ volume E →
      (∀ x ∈ E, |eval (fun i => x i) P| ≤ K ^ 15) →
      ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ K → ‖y‖ ≤ K →
        |eval (fun i => x i) P - eval (fun i => y i) P| ≤ K ^ N * ‖x - y‖ := by
  obtain ⟨N, hN, hcontrol⟩ := exists_polynomial_control 2 1
  refine ⟨N + 15, by omega, ?_⟩
  intro K hK P hP E hE hmass hbound x y hx hy
  have hK0 : 0 ≤ K := by linarith
  have h := (hcontrol K hK P hP E (K ^ 15) (by positivity) hE
    (by simpa only [pow_one] using hmass) hbound).2 x y (by linarith) (by linarith)
  simpa only [← pow_add, mul_assoc] using h

end Submission.Obl.k4_stable_native_signal_oscillation
