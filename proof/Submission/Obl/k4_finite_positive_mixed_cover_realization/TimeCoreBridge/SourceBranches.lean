-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/SourceBranches.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/SourceBranches.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.RootTests
import Submission.Obl.k4_scalar_sign_choice.FiniteSamples
import Submission.Obl.k4_quadratic_atlas_normalization.Curvature

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Set MvPolynomial Submission.Lib.K4QuadraticSheets

/-- A regular nearby root and a small curvature-value error keep the source derivative
away from zero. This is applied on the whole short block before selecting a branch sign. -/
theorem quadratic_source_derivative_floor {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) (x : Fin 4 → ℝ) (w : ℝ) {s E : ℝ} (hs : 0 < s)
    (hroot : eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) P = 0)
    (hder : s ≤ |eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) (pderiv 3 P)|)
    (hfit : |eval x P| ≤ E) (hcurv : 2 * |qc P| * E ≤ s ^ 2 / 2) :
    s ^ 2 / 2 ≤ (eval x (pderiv 3 P)) ^ 2 ∧ eval x (pderiv 3 P) ≠ 0 := by
  have hsource := pderiv_sq_eq_qdisc_add (n := 3) P hP (Fin.init x) (x 3)
  rw [snoc_init_eq] at hsource
  have hroot' := pderiv_sq_eq_qdisc_of_root (n := 3) P hP (Fin.init x) w hroot
  simp only [last_three] at hsource hroot'
  have hsq : s ^ 2 ≤ (eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) (pderiv 3 P)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hs.le hder 2
  have he : (eval x (pderiv 3 P)) ^ 2 - 2 * qc P * eval x P =
      (eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) (pderiv 3 P)) ^ 2 := by
    linear_combination hsource - hroot'
  have hdisc : s ^ 2 ≤ |(eval x (pderiv 3 P)) ^ 2 - 2 * qc P * eval x P| := by
    rw [he, abs_of_nonneg (sq_nonneg _)]
    exact hsq
  have hsmall : 2 * |qc P * eval x P| ≤ s ^ 2 / 2 := by
    rw [abs_mul]
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left hfit (by positivity : 0 ≤ 2 * |qc P|)).trans hcurv
  have hfloor := (Submission.Obl.k4_quadratic_atlas_normalization.low_curvature_derivative_floor
    (sq_pos_of_pos hs) hdisc hsmall).2
  refine ⟨hfloor, ?_⟩
  intro hz
  rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hfloor
  nlinarith [sq_pos_of_pos hs]

/-- The midpoint derivative sign identifies the same branch throughout a short block
on which the original derivative never vanishes. -/
theorem source_derivative_sign_constant {P : MvPolynomial (Fin 4) ℝ}
    (hP : P.totalDegree ≤ 2) (l : ℕ × (Fin 6 → ℝ)) {ta tb t u : ℝ}
    (ht : t ∈ Icc ta tb) (hu : u ∈ Icc ta tb)
    (hnz : ∀ v ∈ Icc ta tb, eval (Submission.Lib.K4XInterface.gx l v) (pderiv 3 P) ≠ 0) :
    0 < eval (Submission.Lib.K4XInterface.gx l t) (pderiv 3 P) *
      eval (Submission.Lib.K4XInterface.gx l u) (pderiv 3 P) := by
  obtain ⟨a, b, hab⟩ := eval_pderiv_gx_affine hP l
  have hcont : Continuous (fun v => eval (Submission.Lib.K4XInterface.gx l v) (pderiv 3 P)) := by
    simpa only [hab] using (show Continuous (fun v : ℝ => a + b * v) by fun_prop)
  have hsign := Submission.Obl.k4_scalar_sign_choice.sign_eq_of_nonzero_interval hcont
    (fun v hv => hnz v (uIcc_subset_Icc ht hu hv))
  rcases lt_or_gt_of_ne (hnz t ht) with hneg | hpos
  · have huneg : eval (Submission.Lib.K4XInterface.gx l u) (pderiv 3 P) < 0 :=
      sign_eq_neg_one_iff.mp (hsign.symm.trans (sign_neg hneg))
    exact mul_pos_of_neg_of_neg hneg huneg
  · have hupos : 0 < eval (Submission.Lib.K4XInterface.gx l u) (pderiv 3 P) :=
      sign_eq_one_iff.mp (hsign.symm.trans (sign_pos hpos))
    exact mul_pos hpos hupos

/-- Equal geometric sign bits on nonzero derivatives choose the same real branch. -/
theorem mul_pos_of_equal_sign_bits {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hbit : decide (0 ≤ a) = decide (0 ≤ b)) : 0 < a * b := by
  by_cases hapos : 0 ≤ a
  · have hbpos : 0 ≤ b := by
      by_contra h
      simp only [hapos, h, decide_true, decide_false] at hbit
      contradiction
    exact mul_pos (lt_of_le_of_ne hapos (Ne.symm ha)) (lt_of_le_of_ne hbpos (Ne.symm hb))
  · have hbneg : ¬0 ≤ b := by
      intro h
      simp only [hapos, h, decide_true, decide_false] at hbit
      contradiction
    exact mul_pos_of_neg_of_neg (not_le.mp hapos) (not_le.mp hbneg)

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
