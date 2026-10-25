import Submission.Obl.k4_finite_row_graph_assembly.FiniteInput

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/Loss.lean.
import Submission.Obl.k4_finite_row_graph_assembly.Ratios

namespace Submission.Obl.k4_finite_row_graph_assembly

def graphDenominator (K R : ℝ) : ℝ := 2048 * K ^ 11 * (6 * R ^ 2 + 2) ^ 4

/-- All losses of the finite construction, isolated from the scale selection. -/
structure LossBounds (K R s L : ℝ) : Prop where
  base : K ≤ L
  ratio : R ^ 3 ≤ L
  endpoint : K + K ^ 2 + 1 ≤ L
  endpoint_count : K * graphDenominator K R ≤ L
  sum_count : K * (10 + 6 * R ^ 3) ^ 2 ≤ L
  rectangle : (6 * R ^ 2 + 2) ^ 2 * K * graphDenominator K R ≤ L
  directions : 512 * K ^ 10 * (R ^ 6) ^ s ≤ L
  witness_mass : 8 * K ^ 5 ≤ L
  witness_error : 2 + K ≤ L

end Submission.Obl.k4_finite_row_graph_assembly
