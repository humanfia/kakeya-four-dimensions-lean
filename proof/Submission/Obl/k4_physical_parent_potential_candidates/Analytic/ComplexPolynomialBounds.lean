-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/ComplexPolynomialBounds.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/ComplexPolynomialBounds.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/ComplexPolynomialBounds.lean
-- Earlier source attributions below are retained.
import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm
import Submission.Obl.k4_algebraic_real_jet_comparison.HolomorphicBounds
import Submission.Obl.k4_quadratic_sheet_continuation.Smooth

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial Metric
open scoped ContDiff

/-- A coefficient bound gives a complex Lipschitz bound with a constant
depending only on degree and dimension. The value estimate and the
holomorphic Lipschitz estimate are both imported accepted results. -/
theorem complex_polynomial_lipschitz_on_unit {n : ℕ} (D : ℕ)
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ D)
    {A : ℝ} (hA : 0 ≤ A) (hcoeff : ∀ m, |P.coeff m| ≤ A)
    {z w : EuclideanSpace ℂ (Fin n)} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖eval (fun i => z i) (P.map (algebraMap ℝ ℂ)) -
      eval (fun i => w i) (P.map (algebraMap ℝ ℂ))‖ ≤
        (4 * (((D + 1 : ℕ) : ℝ) ^ n * (2 : ℝ) ^ D)) * A * ‖z - w‖ := by
  let F : EuclideanSpace ℂ (Fin n) → ℂ :=
    fun u => eval (fun i => u i) (P.map (algebraMap ℝ ℂ))
  have hdiff : DifferentiableOn ℂ F (ball 0 4) := by
    have hsm : ContDiffOn ℂ ⊤ F (ball 0 4) := by
      apply k4_quadratic_sheet_continuation.contDiffOn_polynomial_eval
      intro i
      fun_prop
    exact hsm.differentiableOn (by simp)
  have hbound : ∀ u : EuclideanSpace ℂ (Fin n), ‖u‖ ≤ 2 →
      ‖F u‖ ≤ (((D + 1 : ℕ) : ℝ) ^ n * (2 : ℝ) ^ D) * A := by
    intro u hu
    have hh := Submission.Lib.K4PolynomialRemezThree.norm_complex_eval_le_of_coeff_bound
      n D P hP hA (by norm_num : (1 : ℝ) ≤ 2) hcoeff (fun i => u i)
      (fun i => (PiLp.norm_apply_le u i).trans hu)
    simpa only [eval₂_eq_eval_map] using hh
  have hh := k4_algebraic_real_jet_comparison.holomorphic_inner_lipschitz
    hdiff hbound hw hz
  exact hh.trans_eq (by ring)

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
