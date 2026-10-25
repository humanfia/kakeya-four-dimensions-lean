import Mathlib

/- Adapted from this LOT tree, obligation o107, session x0353, commit 96bcaa7b51cc,
   files Submission/Obl/k4_finite_narrowness_path_improvement/AffinePrimitive.lean
   (affineResidualIntercept, affineResidualSlope) and HorizontalNormalization.lean
   (nativeHorizontalLine): only these three definitions are taken. -/

/-! Native trajectory coordinates and the affine residual of the hidden coordinate. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

def affineResidualIntercept (A : Fin 4 → ℝ) (b : Fin 6 → ℝ) : ℝ :=
  b 2 - A 0 - A 2 * b 0 - A 3 * b 1

def affineResidualSlope (A : Fin 4 → ℝ) (b : Fin 6 → ℝ) : ℝ :=
  b 5 - A 1 - A 2 * b 3 - A 3 * b 4

/-- The base coordinates of the native trajectory in the frozen model. -/
def nativeHorizontalLine (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4]

end

end Submission.Obl.k4_critical_derivative_evaluation_lists
