-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.ComplexPolynomialBounds, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/ComplexPolynomialBounds.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/ComplexPolynomialBounds.lean.
All earlier source attributions below are retained. -/
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

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

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

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
