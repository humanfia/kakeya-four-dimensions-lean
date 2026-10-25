-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/Curvature.lean
import Submission.Obl.k4_quadratic_atlas_normalization.Curvature

/-!
The late curvature dichotomy in the supplied paper's Lemma 3.5.
A high-curvature quadratic is replaced directly by its normalized derivative;
this is the affine critical-center equation, with no root choice required.
-/

namespace Submission.Obl.k4_terminal_label_saturation

open MvPolynomial

variable {σ : Type*}

/-- The constant second derivative in the hidden coordinate. -/
noncomputable def curvature (P : MvPolynomial σ ℝ) (i : σ) : ℝ :=
  (pderiv i (pderiv i P)).coeff 0

theorem second_pderiv_eq_curvature (P : MvPolynomial σ ℝ)
    (hP : P.totalDegree ≤ 2) (i : σ) :
    pderiv i (pderiv i P) = C (curvature P i) := by
  exact Submission.Obl.k4_quadratic_atlas_normalization.second_pderiv_eq_curvature P hP i

end Submission.Obl.k4_terminal_label_saturation
