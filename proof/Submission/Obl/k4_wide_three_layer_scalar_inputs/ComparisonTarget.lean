import Submission.Obl.k4_wide_three_layer_scalar_inputs.Parameters
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Input

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter

/-- The remaining comparison construction. Its exponents are exactly the
ones already fixed by the buffered three-layer datum, before any loss.
The block retains its full original assignment reference. -/
def ComparedPreparation : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Valid →
    ∀ (buffer : ℝ), 100 < buffer →
    ∀ p : Parameters cfg.d cfg.κ cfg.U cfg.e₀ buffer,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        cfg.ProjectedAt k p.s₀ p.s p.u p.v p.R p.M ε) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        Nonempty (Support.ComparedBlock cfg k p.s p.u p.v (cfg.N k ^ (-p.M)) (cfg.N k ^ ε))

end Submission.Obl.k4_wide_three_layer_scalar_inputs
