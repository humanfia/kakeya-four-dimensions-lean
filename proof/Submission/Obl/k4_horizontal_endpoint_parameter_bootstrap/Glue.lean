import Submission.Obl.k4_horizontal_endpoint_parameter_bootstrap.Interfaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_horizontal_endpoint_parameter_bootstrap

/-- At the endpoint rate the rate-family engine has exactly the frozen output. -/
theorem endpoint_to_frozen (h : Endpoint) : EndpointEngine := by
  unfold Endpoint RateEngine at h
  unfold EndpointEngine
  intro N K hN hNlim hK d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he₀
    hcrit hℓκ α mα ν μ ρ π b P T n j A B c F hdata hcaps hforest hnest
  obtain ⟨sMax, R, hsMax, hsU, hse₀, hR, _, hout⟩ :=
    h N K hN hNlim hK d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he₀
      hcrit hℓκ α ν μ ρ π b P T n j A B c F hdata hcaps hforest hnest
  refine ⟨sMax, R, hsMax, hsU, hse₀, hR, ?_⟩
  have hneg : -(2 * κ) = -2 * κ := by ring
  simpa only [hneg] using hout (2 * κ) rfl

end Submission.Obl.k4_horizontal_endpoint_parameter_bootstrap
