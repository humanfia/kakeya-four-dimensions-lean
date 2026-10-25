import Submission.Obl.k4_subcritical_chart_projection.Step
import Submission.Obl.k4_subcritical_chart_projection.ReturnPowers

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory Filter

/-- Scalar returns all three physical layers of the corrected chart
system with one coefficient exponent fixed before every requested loss. -/
theorem scalar_return_rule (hscalar : Scalar) : ReturnRule := by
  intro α inst m hN hNt hK hd hd₁ hκ hκ₁ hbasic hcaps M s₀ depth hs₀ hM hdepth hready
  refine ⟨100 + 100 * s₀, by linarith, ?_⟩
  apply projected_of_chart_steps m (fun k => by linarith [hN k]) hready
  intro h
  exact chart_projection_step hscalar m hN hNt hK.1 hK.2 hd hd₁ hκ hκ₁ hbasic hcaps
    hs₀ hM depth h (hdepth h).1 (hdepth h).2
    (return_numerics_rule m hN hNt hK.1 hK.2 hκ hκ₁ hs₀ hM (hdepth h).2)

end Submission.Obl.k4_subcritical_chart_projection
