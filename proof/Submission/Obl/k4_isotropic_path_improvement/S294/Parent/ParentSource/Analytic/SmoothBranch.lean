-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.SmoothBranch, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/SmoothBranch.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/SmoothBranch.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/SmoothBranch.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/SmoothBranch.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.ComplexBranch

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

/-- The explicit stable quadratic root is smooth to every order for which
its coefficients are smooth. Only the scalar square-root regularity theorem
is needed, even when the domain has several complex dimensions. -/
theorem contDiffOn_stable_quadratic_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : WithTop ℕ∞} (U : Set E) (a : ℂ) (b c : E → ℂ)
    (hb : ContDiffOn ℂ n b U) (hc : ContDiffOn ℂ n c U)
    {β : ℝ} (hβ : 0 < β)
    (hbclose : ∀ z ∈ U, ‖b z - (β : ℂ)‖ ≤ β / 4)
    (hdisc : ∀ z ∈ U, ‖((b z) ^ 2 - 4 * a * c z) - (β : ℂ) ^ 2‖ ≤ β ^ 2 / 4) :
    ContDiffOn ℂ n
      (fun z => -2 * c z / (b z + Complex.sqrt ((b z) ^ 2 - 4 * a * c z))) U := by
  let Δ : E → ℂ := fun z => (b z) ^ 2 - 4 * a * c z
  have hmargins (z : E) (hz : z ∈ U) :=
    stable_quadratic_complex_margins a (b z) (c z) hβ (hbclose z hz) (hdisc z hz)
  have hΔ : ContDiffOn ℂ n Δ U := (hb.pow 2).sub (contDiffOn_const.mul hc)
  have hsqrt : ContDiffOn ℂ n (fun z => Complex.sqrt (Δ z)) U :=
    (Complex.differentiableOn_sqrt.contDiffOn Complex.isOpen_slitPlane).comp hΔ
      (fun z hz => Or.inl (hmargins z hz).1)
  have hden (z : E) (hz : z ∈ U) : b z + Complex.sqrt (Δ z) ≠ 0 :=
    norm_pos_iff.mp (hβ.trans_le (hmargins z hz).2.1)
  exact (contDiffOn_const.mul hc).div (hb.add hsqrt) hden

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
