-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/RealJetEquality.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/RealJetEquality.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/RealJetEquality.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.Assertion

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Metric Filter
open scoped Topology ContDiff

/-- A real-valued complex extension identifies the complete real jets, not
only their norms. This reuses the real-slice adapters proved by x0491. -/
theorem complex_jet_on_real_directions
    {F : EuclideanSpace ℂ (Fin 3) → ℂ} {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : ContDiffOn ℂ ∞ F (ball 0 4))
    (hfF : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 →
      F (DenseJet.realSlice x) = (f x : ℂ))
    (j : ℕ) {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < 4)
    (v : Fin j → EuclideanSpace ℝ (Fin 3)) :
    iteratedFDeriv ℂ j F (DenseJet.realSlice x) (fun i => DenseJet.realSlice (v i)) =
      (iteratedFDeriv ℝ j f x v : ℂ) := by
  have hcx : DenseJet.realSlice x ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4 := by
    simpa only [mem_ball, dist_zero_right, DenseJet.norm_realSlice_apply] using hx
  have hev : (F ∘ DenseJet.realSlice) =ᶠ[𝓝 x] (Complex.ofRealCLM ∘ f) := by
    filter_upwards [isOpen_ball.mem_nhds
      (show x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 4 by
        simpa only [mem_ball, dist_zero_right] using hx)] with y hy
    exact hfF y (by simpa only [mem_ball, dist_zero_right] using hy)
  have heq := (hev.iteratedFDeriv ℝ j).eq_of_nhds
  have hcf := DenseJet.contDiffAt_real_slice hF hfF hx
  have hleft : iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ f) x =
      Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) :=
    Complex.ofRealCLM.iteratedFDeriv_comp_left hcf (by exact_mod_cast le_top)
  rw [DenseJet.iteratedFDeriv_comp_realSlice isOpen_ball hF j hcx,
    DenseJet.iteratedFDeriv_real_eq_restrictScalars isOpen_ball hF j hcx, hleft] at heq
  exact DFunLike.congr_fun heq v

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
