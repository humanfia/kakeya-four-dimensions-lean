import Submission.Obl.k4_physical_row_packet_potential.Glue
import Submission.Obl.k4_physical_row_packet_potential.UniformPrecision

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Glue

/-- Qualified physical rows yield an original-law physical polynomial
potential, with the exponent chosen before all packet data. -/
theorem row_potential_assertion : RowPotentialAssertion := by
  intro M d hd0 hd1
  obtain ⟨C, hC, e, cNorm, cCurl, hpacket⟩ := row_packet_potential_of_numerics M
  obtain ⟨Ep, hEp⟩ := exists_numerics_goal M d hd1 C hC e cNorm cCurl
  exact ⟨Ep, hpacket d hd1 Ep hEp⟩

end Submission.Obl.k4_physical_row_packet_potential.Glue
