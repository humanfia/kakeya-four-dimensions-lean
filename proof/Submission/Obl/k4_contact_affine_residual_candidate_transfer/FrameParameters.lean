import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ResidualFields
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Model

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Filter
open Submission.Obl.k4_critical_switching_state_preparation

/-- The residual frame changes only the loss sequence, depth horizon and
contact exponent among the asymptotic parameters. -/
theorem residualData_parameters {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) {s₀ U' e₀' : ℝ} {K' : ℕ → ℝ}
    (fr : (k : ℕ) → Option (Frame D k s₀ U')) (hU' : 0 < U') (he₀' : 0 < e₀')
    (hK' : (∀ k, 1 ≤ K' k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K' k ≤ D.N k ^ ε) :
    Parameters (residualData D s₀ U' e₀' K' fr) := by
  exact
    { scale := p.scale
      scale_limit := p.scale_limit
      subpower := hK'
      dimension_nonneg := p.dimension_nonneg
      dimension_lt_one := p.dimension_lt_one
      rate_pos := p.rate_pos
      rate_le_one := p.rate_le_one
      transverse_pos := p.rate_pos
      palette_pos := p.palette_pos
      palette_le_one := p.palette_le_one
      depth_pos := hU'
      defect_pos := he₀' }

theorem residualData_equal_rates {α : Type} [MeasurableSpace α]
    (D : Data α) (s₀ U' e₀' : ℝ) (K' : ℕ → ℝ)
    (fr : (k : ℕ) → Option (Frame D k s₀ U')) :
    (residualData D s₀ U' e₀' K' fr).ℓ = (residualData D s₀ U' e₀' K' fr).κ := rfl

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
