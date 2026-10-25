-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/SmoothBranch.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/SmoothBranch.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/SmoothBranch.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.ComplexBranch

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

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

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
