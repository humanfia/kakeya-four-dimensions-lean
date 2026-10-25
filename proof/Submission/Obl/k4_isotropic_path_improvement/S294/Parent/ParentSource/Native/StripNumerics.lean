-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripNumerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripNumerics.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripNumerics.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripNumerics.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripNumerics.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripAtlas
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripGeometryBudget

/-! Derive the refined chart's numerical data bounds from its old chart and
the scalar strip/bin parameters. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Submission.Lib.K4VelocityStrips
open scoped BigOperators RealInnerProductSpace

namespace StripRefinement

variable {α : Type} {W T : ℕ} (d : StripRefinement α) (p : α → StripParent W T)

theorem geometry_budgets {N κ depth H H' S V : ℝ} {M M' D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E)
    (hκ : 1 ≤ κ) (hr : 0 < d.radius) (hH : 1 ≤ H) (hH' : 1 ≤ H')
    (holdH : N ^ M ≤ H) (htime : (2 : ℝ) ^ T ≤ H)
    (he : ∀ b i, ‖d.tangent b i‖ = 1) (hn : ∀ b i, ‖d.normal b i‖ = 1)
    (hen : ∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0)
    (hbins : (d.bins : ℝ) * d.radius ≤ S) (hβ : ∀ b i, |d.offset b i| ≤ V)
    (hSV : S + 2 * V ≤ H') (hcenter : 4 * H ^ 2 * H' ≤ N ^ M')
    (hentry : N ^ M * (2 * (κ + (1 + (d.normalBudget : ℝ)) * d.radius + κ⁻¹ +
      ((1 + (d.normalBudget : ℝ)) * d.radius)⁻¹)) ≤ N ^ M')
    {κ' : ℝ} (hsize : κ * (2 * (κ + (1 + (d.normalBudget : ℝ)) * d.radius)) ≤ κ')
    (a : d.Label) :
    ‖d.center p a‖ + ‖d.velocity p a‖ ≤ N ^ M' ∧
    (∑ i : Fin 2, ∑ j : Fin 2, (|d.frame p κ a i j| + |(d.frame p κ a)⁻¹ i j|)) ≤ N ^ M' ∧
    (∑ i : Fin 2, ∑ j : Fin 2, |d.frame p κ a i j|) ≤ κ' / (2 : ℝ) ^ T := by
  rcases hold a.1 with ⟨_, hcu, hframe, hsmall, _⟩
  have hQ : (∑ i : Fin 2, ∑ j : Fin 2, |(p a.1).frame i j|) ≤ N ^ M := by
    have hnonneg : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, |((p a.1).frame)⁻¹ i j| :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    simpa only [Finset.sum_add_distrib] using (show
      (∑ i : Fin 2, ∑ j : Fin 2, |(p a.1).frame i j|) ≤ N ^ M from by
        simp only [Finset.sum_add_distrib] at hframe
        linarith)
  have ht : |(p a.1).start| ≤ 1 := by
    have hpos : 0 < (2 : ℝ) ^ T := by positivity
    have hj : ((p a.1).timeIndex : ℝ) ≤ (2 : ℝ) ^ T := by
      exact_mod_cast (p a.1).timeIndex.isLt.le
    unfold StripParent.start
    rw [abs_of_nonneg (by positivity : 0 ≤ ((p a.1).timeIndex : ℝ) / (2 : ℝ) ^ T)]
    exact (div_le_one hpos).mpr hj
  have hs : |((a.2.2 : ℤ) : ℝ) * d.radius| + 2 * |d.offset a.1 a.2.1| ≤ H' := by
    exact (add_le_add ((stripBinRange_center_budget hr.le a.2.2.property).trans hbins)
      (mul_le_mul_of_nonneg_left (hβ _ _) (by norm_num))).trans hSV
  refine ⟨?_, ?_, ?_⟩
  · exact (physicalStrip_center_velocity_budget hH hH' ht
      (by simpa only [inv_inv, abs_of_pos (show 0 < (2 : ℝ) ^ T by positivity)] using htime)
      (hcu.trans holdH) (hQ.trans holdH) (hn _ _) hs).trans hcenter
  · exact (strip_physical_frame_entry_budget (by linarith) (by positivity) hr
      (he _ _) (hn _ _) (hen _ _) hframe).trans hentry
  · exact (strip_physical_frame_size_budget (by linarith) (by positivity) hr
      (he _ _) (hn _ _) hsmall).trans (div_le_div_of_nonneg_right hsize (by positivity))

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
