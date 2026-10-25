-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/QuadraticRoots.lean
import Submission.Obl.k4_stable_native_signal_oscillation.Hidden

/-! Real quadratic root identities used before introducing simple sheets. -/

namespace Submission.Obl.k4_terminal_label_saturation

/-- Exact Taylor expansion of a quadratic about an arbitrary point. -/
theorem quadratic_taylor (p : Polynomial ℝ) (hp : p.natDegree ≤ 2) (x t : ℝ) :
    p.eval (x + t) = p.eval x + p.derivative.eval x * t +
      p.derivative.derivative.eval x / 2 * t ^ 2 := by
  convert Submission.Obl.k4_stable_native_signal_oscillation.polynomial_quadratic_taylor
    p hp x t using 1 <;> ring

/-- The derivative of a quadratic has its exact affine Taylor expansion. -/
theorem quadratic_derivative_taylor (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    (x t : ℝ) :
    p.derivative.eval (x + t) =
      p.derivative.eval x + p.derivative.derivative.eval x * t := by
  obtain ⟨a, b, c, rfl⟩ := Submission.Lib.K4QuadraticSublevel.quadratic_eq_coefficients p hp
  simp [Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring

end Submission.Obl.k4_terminal_label_saturation
