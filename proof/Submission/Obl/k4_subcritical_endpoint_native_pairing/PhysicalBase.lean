import Mathlib

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

/-- Physical base coordinates of the original trajectory. -/
def parameterPhysicalBase {α : Type*} (b : α → Fin 6 → ℝ) (z : α × ℝ) : Fin 3 → ℝ :=
  ![z.2, b z.1 0 + z.2 * b z.1 3, b z.1 1 + z.2 * b z.1 4]

end Submission.Obl.k4_subcritical_endpoint_native_pairing
