-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.OriginalAtlasMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/OriginalAtlasMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/OriginalAtlasMass.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/OriginalAtlasMass.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedMass

/-! A geometric cover counts mass in the ORIGINAL input residual. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StripRefinement

variable {α : Type} [Fintype α] {W T : ℕ}
  (d : StripRefinement α) (p : α → StripParent W T)

theorem weighted_merged_original_inter_mass_le
    (μ : Fin W → Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (ω : Fin W → ℝ) (width : ℝ)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (R H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hRH : ∀ w, R w ⊆ H w)
    (hcover : ∀ w, R w ⊆ {x | ∃ a : d.MergedLabel,
      (p a.1).world = w ∧ x ∈ d.mergedIncidence p width success a}) :
    (∑ w, ENNReal.ofReal (ω w) * μ w (R w)) ≤
      ∑ a : d.MergedLabel, ENNReal.ofReal (ω (p a.1).world) *
        μ (p a.1).world (d.mergedIncidence p width success a ∩ H (p a.1).world) := by
  classical
  have h := weighted_residual_mass_le_sum μ ω (fun _a : d.MergedLabel => 0)
    (fun a => (p a.1).world) (d.mergedIncidence p width success) R 0 (fun w x hx => by
      obtain ⟨a, hγ, ha⟩ := hcover w hx
      exact ⟨a, rfl, hγ, ha⟩)
  calc
    _ ≤ ∑ a : d.MergedLabel, ENNReal.ofReal (ω (p a.1).world) *
        μ (p a.1).world (R (p a.1).world ∩ d.mergedIncidence p width success a) := by
      simpa only [ite_true] using h
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply measure_mono
      intro x hx
      exact ⟨hx.2, hRH _ hx.1⟩

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
