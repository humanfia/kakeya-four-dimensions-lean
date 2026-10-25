-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/DiscriminantDegree.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.PolynomialSheets
import Submission.Obl.k4_bounded_sign_choice.PolynomialFamily

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial

theorem disc_totalDegree_le (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) :
    (disc P).totalDegree ≤ 2 := by
  have hraw : (pderiv (3 : Fin 4) P) ^ 2 -
      2 * pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P) * P =
      Submission.Obl.k4_quadratic_atlas_normalization.discriminant P (3 : Fin 4) := by
    rw [Submission.Obl.k4_quadratic_atlas_normalization.second_pderiv_eq_curvature P hP]
    unfold Submission.Obl.k4_quadratic_atlas_normalization.discriminant
    rw [map_mul, map_ofNat]
  unfold disc
  rw [hraw]
  apply (Submission.Obl.k4_bounded_sign_choice.totalDegree_eval₂_le
    (Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) X) ?_ _).trans
    (Submission.Obl.k4_quadratic_atlas_normalization.discriminant_totalDegree P hP _)
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (0 : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1
    simp
  · simp

end Submission.Obl.k4_paired_test_normalization
