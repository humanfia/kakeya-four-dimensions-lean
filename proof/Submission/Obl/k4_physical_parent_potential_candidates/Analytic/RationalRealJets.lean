-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/RationalRealJets.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/RationalRealJets.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/RationalRealJets.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.IteratedRational
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.RealJetEquality
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.SampledBranch

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial Metric
open scoped ContDiff

/-- Rational quadratic-extension data supply the exact algebraic real
extension required by the sampled certificate, for every directional jet.
The degree depends only on the initial polynomial degree and jet order. -/
theorem hasRealExtension_rational_directional_jet (D : ℕ)
    (Δ U V W : MvPolynomial (Fin 3) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (hΔne : Δ ≠ 0) (hWne : W ≠ 0)
    (s F : EuclideanSpace ℂ (Fin 3) → ℂ)
    (hs : DifferentiableOn ℂ s (ball 0 4))
    (hF : ContDiffOn ℂ ⊤ F (ball 0 4))
    (hroot : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (s z) ^ 2 = eval (fun i => z i) Δ)
    (hrep : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (fun i => z i) W * F z =
        eval (fun i => z i) U + eval (fun i => z i) V * s z)
    (f : Base → ℝ)
    (hfF : ∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ))
    (v : Base) (k : ℕ) :
    HasRealExtension (8 * (3 ^ k * D) + 2)
      (fun x => iteratedFDeriv ℝ k f x (fun _ => v)) := by
  obtain ⟨P, hPne, hPdeg, hPrel⟩ := exists_iterated_frechet_relation D Δ U V W
    hΔ hU hV hW hΔne hWne (ball 0 4) isOpen_ball s F hs hF hroot hrep
    (DenseJet.realSlice v) k
  refine ⟨(fun z => iteratedFDeriv ℂ k F z (fun _ => DenseJet.realSlice v)),
    P, hPne, hPdeg, contDiffOn_complex_jet_apply isOpen_ball hF k _, hPrel, ?_⟩
  intro x hx
  exact complex_jet_on_real_directions (hF.of_le le_top)
    (fun y hy => hfF y (by simpa only [mem_ball, dist_zero_right] using hy))
    k (by simpa only [mem_ball, dist_zero_right] using hx) (fun _ => v)

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
