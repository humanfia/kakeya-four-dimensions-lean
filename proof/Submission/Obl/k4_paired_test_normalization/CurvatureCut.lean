-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/CurvatureCut.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.DiscriminantFloors

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization

/-- Retain the small-curvature test and replace every other test by its affine
critical-center equation in hidden derivative unit one. -/
noncomputable def curvatureCut (P : MvPolynomial (Fin 4) ℝ) (c : ℝ) :
    MvPolynomial (Fin 4) ℝ :=
  if |curvature P (3 : Fin 4)| ≤ c then P else criticalCenterTest P 3 1

private theorem critical_center_disc (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (hc : curvature P (3 : Fin 4) ≠ 0) :
    disc (criticalCenterTest P 3 1) = 1 := by
  simp [disc, criticalCenterTest_pderiv P hP 3 1 hc]

/-- All global coefficient/curvature bounds and all pointwise tests survive
the replacement, with the original low-case residual in the cross term. -/
theorem curvatureCut_bounds (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {c V : ℝ} (hc : 0 < c) (hV : 0 ≤ V) (hcoeff : ∀ m, |P.coeff m| ≤ V) :
    (curvatureCut P c).totalDegree ≤ 2 ∧
    |curvature (curvatureCut P c) (3 : Fin 4)| ≤ c ∧
    (∀ m, |(curvatureCut P c).coeff m| ≤ max V (2 * V / c)) ∧
    ∀ (z : Fin 4 → ℝ) (ρ U : ℝ), 0 ≤ ρ → 0 ≤ U →
      |eval z P| ≤ ρ → |eval z (pderiv (3 : Fin 4) P)| ≤ U →
      |eval z (curvatureCut P c)| ≤ max ρ (U / c) ∧
      |eval z (pderiv (3 : Fin 4) (curvatureCut P c))| ≤ max U 1 ∧
      2 * |curvature (curvatureCut P c) (3 : Fin 4) * eval z (curvatureCut P c)| ≤
        2 * c * ρ := by
  classical
  by_cases hlow : |curvature P (3 : Fin 4)| ≤ c
  · rw [curvatureCut, if_pos hlow]
    refine ⟨hP, hlow, fun m => (hcoeff m).trans (le_max_left _ _), ?_⟩
    intro z ρ U hρ hU hvalue hderiv
    refine ⟨hvalue.trans (le_max_left _ _), hderiv.trans (le_max_left _ _), ?_⟩
    rw [abs_mul]
    have h := mul_le_mul hlow hvalue (abs_nonneg _) hc.le
    nlinarith
  · have hhigh : c ≤ |curvature P (3 : Fin 4)| := (lt_of_not_ge hlow).le
    have hne : curvature P (3 : Fin 4) ≠ 0 := by
      intro heq
      rw [heq, abs_zero] at hhigh
      linarith
    rw [curvatureCut, if_neg hlow]
    have hcurv : curvature (criticalCenterTest P 3 1) (3 : Fin 4) = 0 := by
      unfold curvature
      rw [criticalCenterTest_second_pderiv P hP 3 1 hne]
      simp
    refine ⟨(criticalCenterTest_totalDegree P hP 3 1).trans (by norm_num),
      by simpa only [hcurv, abs_zero] using hc.le, ?_, ?_⟩
    · intro m
      apply le_trans _ (le_max_right V (2 * V / c))
      simpa only [mul_one] using
        criticalCenterTest_coeff_bound P hP 3 (by norm_num : (0 : ℝ) ≤ 1)
          hc hhigh hV hcoeff m
    · intro z ρ U hρ hU hvalue hderiv
      refine ⟨?_, ?_, ?_⟩
      · apply le_trans _ (le_max_right ρ (U / c))
        simpa only [one_mul] using
          criticalCenterTest_eval_bound P 3 (by norm_num : (0 : ℝ) ≤ 1) hc hhigh z hderiv
      · rw [criticalCenterTest_pderiv P hP 3 1 hne, eval_C, abs_one]
        exact le_max_right _ _
      · rw [hcurv, zero_mul, abs_zero, mul_zero]
        positivity

/-- Every raw regular test point has a signed discriminant floor after the
curvature replacement, including the high-curvature affine case. -/
theorem curvatureCut_disc_floor (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (w : ℝ) {c B ρ : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (hderiv : B ≤ |eval (Fin.snoc z w) (pderiv (3 : Fin 4) P)|)
    (hvalue : |eval (Fin.snoc z w) P| ≤ ρ) (hsmall : 2 * c * ρ ≤ B ^ 2 / 2) :
    min (B ^ 2 / 2) 1 ≤ eval z (disc (curvatureCut P c)) := by
  classical
  by_cases hlow : |curvature P (3 : Fin 4)| ≤ c
  · rw [curvatureCut, if_pos hlow]
    exact (min_le_left _ _).trans
      (disc_floor_of_derivative P hP z w hB hderiv hlow hvalue hsmall)
  · have hne : curvature P (3 : Fin 4) ≠ 0 := by
      intro heq
      apply hlow
      simpa only [heq, abs_zero] using hc.le
    rw [curvatureCut, if_neg hlow, critical_center_disc P hP hne, map_one]
    exact min_le_right _ _

end Submission.Obl.k4_paired_test_normalization
