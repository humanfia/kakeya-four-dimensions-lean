-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.OriginalDeletion, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/OriginalDeletion.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/OriginalDeletion.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/OriginalDeletion.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Preparation

/-! Original-law deletion bounds with an arbitrary explicit loss budget. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

theorem mixture_le_sdiff_add {Γ X : Type*} [Fintype Γ] [MeasurableSpace X]
    (μ : Γ → Measure X) (weight : Γ → ENNReal) (H bad : Γ → Set X) :
    (∑ w, weight w * μ w (H w)) ≤
      (∑ w, weight w * μ w (H w \ bad w)) + ∑ w, weight w * μ w (bad w) := by
  calc
    _ ≤ ∑ w, weight w * (μ w (H w \ bad w) + μ w (bad w)) := by
      apply Finset.sum_le_sum
      intro w _
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply (measure_mono _).trans (measure_union_le _ _)
      intro x hx
      by_cases hb : x ∈ bad w
      · exact Or.inr hb
      · exact Or.inl ⟨hx, hb⟩
    _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib]

/-- A finite explicit loss is charged in the unchanged weighted mixture. -/
theorem mixture_remove_budget {Γ X : Type*} [Fintype Γ] [MeasurableSpace X]
    (μ : Γ → Measure X) (weight : Γ → ENNReal) (H bad : Γ → Set X)
    {a loss : ENNReal} (hloss : loss ≠ ∞)
    (hH : a + loss ≤ ∑ w, weight w * μ w (H w))
    (hbad : (∑ w, weight w * μ w (bad w)) ≤ loss) :
    a ≤ ∑ w, weight w * μ w (H w \ bad w) := by
  apply ENNReal.le_of_add_le_add_right hloss
  exact hH.trans ((mixture_le_sdiff_add μ weight H bad).trans (add_le_add le_rfl hbad))

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
