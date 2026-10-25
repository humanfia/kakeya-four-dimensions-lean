import Mathlib
import ChallengeDeps

/-!
A smooth version of polynomial directional area, using arctan as a
bounded approximation to the sign function.  Only ambient volume and
the ordinary derivative occur.  This analytic formulation was suggested
by LOT session x0033 at 2026-10-21T02:18Z.
-/

namespace Submission.Obl.k4_mk_visibility

noncomputable def directionalVariation {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (c v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict (Metric.ball c 1))
    (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        Real.arctan (MvPolynomial.eval (fun j => y j) p)) x v‖)

end Submission.Obl.k4_mk_visibility
