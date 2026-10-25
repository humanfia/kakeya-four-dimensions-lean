import Submission.Obl.k4_quadratic_sheet_continuation.TubeCalculus

namespace Submission.Obl.k4_quadratic_sheet_continuation

/-- The exact dimension-by-dimension interface for the calculus step. -/
theorem directional_jet_path_transfer :
    ∀ n N s : ℕ, ∀ K : ℝ, 0 < K → ∃ q : ℕ, ∃ L : ℝ,
      max s N ≤ q ∧ 0 < L ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ a b c : EuclideanSpace ℂ (Fin n), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
      ∀ H : EuclideanSpace ℂ (Fin n) → ℂ,
      (fun U : Set (EuclideanSpace ℂ (Fin n)) =>
        ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) H U →
        (∀ p v : EuclideanSpace ℂ (Fin n),
          (∀ t ∈ Metric.thickening ((8 * A)⁻¹) (segment ℝ (0 : ℂ) 1), p + t • v ∈ U) →
          ∀ V : ℝ, 0 ≤ V →
            (∀ j : ℕ, j ≤ N → ‖iteratedDeriv j (fun t : ℂ => H (p + t • v)) 0‖ ≤ V) →
            ‖H (p + v)‖ ≤ (8 * A) ^ K * V) →
        ∀ V : ℝ, 0 ≤ V →
          (((∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ V) →
            (∀ z ∈ Metric.closedBall c ((8 * A)⁻¹), ‖H z‖ ≤ A ^ L * V) ∧
            ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ A ^ L * V) ∧
          ((∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ V) →
            ∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ A ^ L * V)))
      (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) := by
  intro n N s K hK
  obtain ⟨q, C, hs, hN, hC, h⟩ := tube_norm_jet_comparison_of_directional N s K hK
  exact ⟨q, C, max_le hs hN, hC, h n⟩

end Submission.Obl.k4_quadratic_sheet_continuation
