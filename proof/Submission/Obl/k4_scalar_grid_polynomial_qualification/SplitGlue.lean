import Submission.Obl.k4_scalar_grid_polynomial_qualification.DiscoveryInterfaceBridge
import Submission.Obl.k4_scalar_grid_polynomial_qualification.FirstJetInterfaceBridge
import Submission.Obl.k4_scalar_grid_polynomial_qualification.JetInterfaceBridge
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Assembly
import Submission.Obl.k4_scalar_normal_first_jet
import Submission.Obl.k4_scalar_graph_residual_discovery

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

/-- The proved jet assembly supplies the quantitative fitting interface. -/
theorem higherJetInput_of_firstJetInput (h : FirstJetInput) : HigherJetInput :=
  higherJetInput_iff.mpr (Jets.higher_jets_of_first_jet (firstJetInput_iff.mp h))

/-- The two analytic children compose through the proved higher-jet assembly. -/
theorem discoveryInput_of_children : DiscoveryInput :=
  Submission.k4_scalar_graph_residual_discovery
    (higherJetInput_of_firstJetInput Submission.k4_scalar_normal_first_jet)

theorem polynomialDiscovery_of_children : PolynomialDiscoveryStatement :=
  polynomialDiscovery_of_closed discoveryInput_of_children

end Submission.Obl.k4_scalar_grid_polynomial_qualification
