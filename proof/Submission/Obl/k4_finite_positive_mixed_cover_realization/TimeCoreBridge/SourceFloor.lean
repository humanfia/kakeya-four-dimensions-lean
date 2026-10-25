-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/SourceFloor.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o173/x0598, commit b7284666,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/SourceFloor.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.LowCurvatureNumerics
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.SourceBranches

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial Set Submission.Lib.K4QuadraticSheets

/-- After the stable sheet has been constructed, its regular root and the low
cutoff force the original source derivative to be nonzero. The sheet fit itself
is not needed, so this precedes the branch-sign argument. -/
theorem low_curvature_source_nonzero {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) {A a_fit : ℝ} (hA : 2 ≤ A)
    (hsmall : |qc P / 2| * a_fit ≤ A ^ (-20 : ℝ))
    (x : Fin 4 → ℝ) (w : ℝ)
    (hroot : eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) P = 0)
    (hder : A ^ (-1 : ℝ) ≤ |eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) (pderiv 3 P)|)
    (hfit : |eval x P| ≤ a_fit * A) : eval x (pderiv 3 P) ≠ 0 := by
  exact (quadratic_source_derivative_floor hP x w
    (Real.rpow_pos_of_pos (by linarith : 0 < A) _) hroot hder hfit
    (low_curvature_error_budget hA hsmall)).2

/-- Positive products identify the same nonnegative derivative sign bit. -/
theorem sign_bits_eq_of_mul_pos {a b : ℝ} (h : 0 < a * b) :
    decide (0 ≤ a) = decide (0 ≤ b) := by
  rcases mul_pos_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp only [show 0 ≤ a from ha.le, show 0 ≤ b from hb.le]
  · simp only [show ¬0 ≤ a from not_le.mpr ha, show ¬0 ≤ b from not_le.mpr hb]

/-- Two member lines with the same midpoint sign bit stay on the same real
branch at all their short-block times. -/
theorem source_derivative_same_branch {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) (l l0 : ℕ × (Fin 6 → ℝ)) {ta tb t t0 : ℝ}
    (ht : t ∈ Icc ta tb) (ht0 : t0 ∈ Icc ta tb) (hab : ta ≤ tb)
    (hnz : ∀ v ∈ Icc ta tb, eval (Submission.Lib.K4XInterface.gx l v) (pderiv 3 P) ≠ 0)
    (hnz0 : ∀ v ∈ Icc ta tb, eval (Submission.Lib.K4XInterface.gx l0 v) (pderiv 3 P) ≠ 0)
    (hbit : decide (0 ≤ eval (Submission.Lib.K4XInterface.gx l ((ta + tb) / 2)) (pderiv 3 P)) =
      decide (0 ≤ eval (Submission.Lib.K4XInterface.gx l0 ((ta + tb) / 2)) (pderiv 3 P))) :
    0 < eval (Submission.Lib.K4XInterface.gx l t) (pderiv 3 P) *
      eval (Submission.Lib.K4XInterface.gx l0 t0) (pderiv 3 P) := by
  have hmid : (ta + tb) / 2 ∈ Icc ta tb := ⟨by linarith, by linarith⟩
  have hleft := sign_bits_eq_of_mul_pos (source_derivative_sign_constant hP l ht hmid hnz)
  have hright := sign_bits_eq_of_mul_pos (source_derivative_sign_constant hP l0 hmid ht0 hnz0)
  exact mul_pos_of_equal_sign_bits (hnz t ht) (hnz0 t0 ht0) (hleft.trans (hbit.trans hright))

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
