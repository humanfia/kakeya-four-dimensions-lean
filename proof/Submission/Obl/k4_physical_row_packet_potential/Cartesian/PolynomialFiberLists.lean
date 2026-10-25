import Submission.Lib.K4PolynomialFiberLists.FiberLists
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.LocalListPacking

/-! Reuse the accepted polynomial-fit coefficient-list API. -/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

export Submission.Lib.K4PolynomialFiberLists
  (exists_univariate_coefficient_bound coefficient_bound_of_unit_witness
    polynomial_sublevel_mass_lt polynomial_fit_packing polynomialFitCoefficients
    polynomialFitCoefficientCode fiberFitConditioning polynomial_fit_coefficient_bins
    polynomial_fit_list_power_bound)

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
