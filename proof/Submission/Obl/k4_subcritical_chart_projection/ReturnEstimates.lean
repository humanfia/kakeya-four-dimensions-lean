import Submission.Obl.k4_subcritical_chart_projection.Model

namespace Submission.Obl.k4_subcritical_chart_projection

open Filter

/-- The seven purely numerical bounds needed to return a corrected layer
and retain a dense law. The coefficient exponent `R` is fixed before the loss. -/
structure ReturnEstimates (N K κ s₀ depth M ξ τ ε R : ℝ) : Prop where
  fine : 2 * N ^ (-M) ≤ N ^ (-(2 * κ * s₀))
  corner : 3 * N ^ ξ + 3 ≤ N ^ ε
  norm : 5 * N ^ ξ + N ^ (-s₀) * (150 * (240 * (N ^ τ) ^ 5)) ≤ N ^ ε
  fit : N ^ (-s₀) * (N ^ τ * N ^ (-(depth - s₀)) +
      4 * (240 * (N ^ τ) ^ 5) * 4 * ((N ^ (-M) + N ^ (-M)) / N ^ (-(2 * κ * s₀)))) +
    (2 * N ^ ξ / N ^ (-(2 * κ * s₀)) * N ^ (-M) +
      2 * N ^ ξ / N ^ (-(2 * κ * s₀)) * (N ^ (-M) + N ^ (-M))) ≤
        N ^ ε * N ^ (-depth)
  coeff : 6 * ((2 * (N ^ ξ + 2 * N ^ ξ / N ^ (-(2 * κ * s₀)) * (2 * (N ^ ξ + 1) + 1))) *
      (1 + 2 * (N ^ ξ + 1))) +
    N ^ (-s₀) * (9 * (240 * (N ^ τ) ^ 5) *
      ((1 + 4 * (N ^ ξ + 1)) / N ^ (-(2 * κ * s₀))) ^ 2) ≤ N ^ R
  budget : 4 * (N ^ τ) ^ 2 * K ≤ N ^ ε
  remaining : N ^ (-ε) + (N ^ ε)⁻¹ * (4 * (N ^ τ) ^ 2 * K) ≤ N ^ (-2 * τ)

/-- One choice of Scalar loss and a maximum chart loss gives the return
estimates eventually, uniformly over all smaller positive chart losses. -/
def ReturnNumericsRule {α : Type} [MeasurableSpace α] (m : Model α)
    (M s₀ R depth : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, 0 < τ ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧
    ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ᶠ k in atTop,
      ReturnEstimates (m.N k) (m.K k) m.κ s₀ depth M ξ τ ε R

end Submission.Obl.k4_subcritical_chart_projection
