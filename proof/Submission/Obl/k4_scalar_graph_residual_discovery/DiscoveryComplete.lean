import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryPowerExistence
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryParameters
import Submission.Obl.k4_scalar_graph_residual_discovery.NumericalAssembly

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

/-- The raw finite selection cost and all later geometric powers fit in
an arbitrary positive exponent budget. The first grid also has the fixed
smallness needed for the independently chosen graph precision. -/
theorem discovery_power_existence : DiscoveryPowerExistenceStatement := by
  intro N H Hg K hN hNt hH hHg hK d S Cmk hd hS hCmk C₁ C α δ hα hδ
  let α₀ : ℝ := min α 1
  have hα₀ : 0 < α₀ := lt_min hα zero_lt_one
  have hα₀α : α₀ ≤ α := min_le_left _ _
  have hα₀one : α₀ ≤ 1 := min_le_right _ _
  obtain ⟨J₂, J₁, hJ₂, hJ₁, ω, τ, hω, hτ, _, _, hrel,
    hselection, hcap, hsupport, htime, hresidual⟩ := exists_discovery_parameters C hα₀ hS
  refine ⟨J₁, J₂, hJ₁, hJ₂, by linarith, τ, hτ, ?_⟩
  exact DiscoveryPowerSchedule.eventually_power_bounds hN hNt hK hH hHg hd hδ hα hCmk
    hω hτ hrel C₁ C J₁ J₂ (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)

/-- The numerical original-world discovery certificate exists with graph
precision fixed before every later accuracy and failure-loss budget. -/
theorem discovery_budget_existence : DiscoveryBudgetExistenceStatement :=
  discovery_budgets_of_power_existence discovery_power_existence

end Submission.Obl.k4_scalar_graph_residual_discovery
