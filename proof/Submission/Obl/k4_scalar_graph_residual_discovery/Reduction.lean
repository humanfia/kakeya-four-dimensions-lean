import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryInterfaceBridge
import Submission.Obl.k4_scalar_graph_residual_discovery.JetInterfaceBridge
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldDiscoveryAssembly

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

/-- o278 reduces to the geometric world producer `OriginalWorldPreparationStatement`:
the higher-jet input converts to `Jets.HigherJetsStatement`, the checked world
consumer gives `PolynomialDiscoveryStatement`, and the bridge returns the frozen
Mathlib-only discovery interface. -/
theorem discoveryFromHigherJets_of_worldPreparation
    (hworld : OriginalWorldPreparationStatement) : DiscoveryFromHigherJets := fun h =>
  discoveryInput_of_polynomialDiscovery
    (polynomialDiscovery_of_original_preparation (higherJetInput_iff.mp h) hworld)

end Submission.Obl.k4_scalar_graph_residual_discovery
