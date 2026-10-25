import Submission.Obl.k4_scalar_grid_parameter_preparation.FrozenAdapters
import Submission.Obl.k4_scalar_grid_parameter_preparation.CoefficientPriorCaps

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

theorem coeffTag_eq (N r : ℝ) (l : ℕ × (Fin 5 → ℝ)) :
    coeffTag N r l = scalarMixedCoefficientTag (N ^ (-r)) (N ^ (-r)) l.2 := by
  ext e
  simp only [coeffTag,scalarMixedCoefficientTag,ite_self]

end Submission.Obl.k4_scalar_grid_parameter_preparation
