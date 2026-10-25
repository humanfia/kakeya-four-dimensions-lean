-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PaletteTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PaletteTransfer.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PaletteTransfer.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PaletteTransfer.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/PaletteTransfer.lean.
   Original comments and attributions are preserved below. -/
import Mathlib

/-! A finite ambiguity bound permits a change of velocity palette with an
explicit original-mass cost. All reference marginals stay fixed. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open scoped BigOperators

noncomputable def paletteRefinementRetained {E Z Y : Type*}
    (T : E → Z → Y → ℝ) (π : Z → Y → ℝ) (πZ : Z → ℝ) (ε : ℝ)
    (e : E) (z : Z) (y : Y) : ℝ := by
  classical
  exact if ε * πZ z ≤ π z y then T e z y else 0

theorem paletteRefinementRetained_bounds {E Z Y : Type*}
    (T : E → Z → Y → ℝ) (π : Z → Y → ℝ) (πZ : Z → ℝ) (ε : ℝ)
    (hT : ∀ e z y, 0 ≤ T e z y) (e : E) (z : Z) (y : Y) :
    0 ≤ paletteRefinementRetained T π πZ ε e z y ∧
      paletteRefinementRetained T π πZ ε e z y ≤ T e z y := by
  classical
  unfold paletteRefinementRetained
  split_ifs
  · exact ⟨hT e z y, le_rfl⟩
  · exact ⟨le_rfl, hT e z y⟩

/-- The retained new-palette joint mass is capped by the ORIGINAL fine-state
weight and ORIGINAL new-palette marginal. The factor is `R/ε`. -/
theorem paletteRefinement_joint_cap {E Z Y : Type*} [Fintype Z]
    (T : E → Z → Y → ℝ) (π : Z → Y → ℝ) (πZ : Z → ℝ) (w : E → ℝ)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (hw : ∀ e, 0 ≤ w e)
    (hπ : ∀ z y, 0 ≤ π z y)
    (hOld : ∀ e z y, T e z y ≤ R * w e * πZ z) (e : E) (y : Y) :
    (∑ z, paletteRefinementRetained T π πZ ε e z y) ≤
      (R / ε) * w e * ∑ z, π z y := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  by_cases hkeep : ε * πZ z ≤ π z y
  · rw [paletteRefinementRetained, if_pos hkeep]
    have hpi : πZ z ≤ π z y / ε := (le_div_iff₀ hε).mpr (by nlinarith)
    calc
      _ ≤ R * w e * πZ z := hOld e z y
      _ ≤ R * w e * (π z y / ε) :=
        mul_le_mul_of_nonneg_left hpi (mul_nonneg hR (hw e))
      _ = _ := by ring
  · rw [paletteRefinementRetained, if_neg hkeep]
    exact mul_nonneg (mul_nonneg (div_nonneg hR hε.le) (hw e)) (hπ z y)

/-- If at most `K` new labels occur over each original label, removing the
small conditional pieces costs at most `ε*K` times the old total mass.
The fine-state masses need only be dominated by the old joint marginal. -/
theorem paletteRefinement_lost_mass {E Z Y : Type*}
    [Fintype E] [Fintype Z] [Fintype Y]
    (T : E → Z → Y → ℝ) (π : Z → Y → ℝ) (πZ : Z → ℝ)
    {ε : ℝ} (hε : 0 < ε) (hπZ : ∀ z, 0 ≤ πZ z)
    (hmarginal : ∀ z y, (∑ e, T e z y) ≤ π z y) (K : ℕ)
    (hK : ∀ z, (Finset.univ.filter (fun y => 0 < π z y)).card ≤ K) :
    (∑ e, ∑ z, ∑ y, (T e z y - paletteRefinementRetained T π πZ ε e z y)) ≤
      ε * (K : ℝ) * ∑ z, πZ z := by
  classical
  have hterm (z : Z) (y : Y) :
      (∑ e, (T e z y - paletteRefinementRetained T π πZ ε e z y)) ≤
        if 0 < π z y then ε * πZ z else 0 := by
    by_cases hkeep : ε * πZ z ≤ π z y
    · simp only [paletteRefinementRetained, hkeep, if_true, sub_self, Finset.sum_const_zero]
      split_ifs
      · exact mul_nonneg hε.le (hπZ z)
      · exact le_rfl
    · simp only [paletteRefinementRetained, hkeep, if_false, sub_zero]
      by_cases hpos : 0 < π z y
      · rw [if_pos hpos]
        exact (hmarginal z y).trans (le_of_not_ge hkeep)
      · rw [if_neg hpos]
        exact (hmarginal z y).trans (le_of_not_gt hpos)
  have hlabel (z : Z) :
      (∑ y, ∑ e, (T e z y - paletteRefinementRetained T π πZ ε e z y)) ≤
        (K : ℝ) * (ε * πZ z) := by
    calc
      _ ≤ ∑ y, if 0 < π z y then ε * πZ z else 0 :=
        Finset.sum_le_sum (fun y _ => hterm z y)
      _ = ((Finset.univ.filter (fun y => 0 < π z y)).card : ℝ) * (ε * πZ z) := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hK z))
        (mul_nonneg hε.le (hπZ z))
  calc
    _ = ∑ z, ∑ y, ∑ e, (T e z y - paletteRefinementRetained T π πZ ε e z y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      exact Finset.sum_comm
    _ ≤ ∑ z, (K : ℝ) * (ε * πZ z) := Finset.sum_le_sum (fun z _ => hlabel z)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

/-- Change palette by keeping whole `(old,new)` states. The omitted mass is
charged to their ORIGINAL coupling; the new joint cap uses original marginals. -/
theorem palette_refinement_prepare {E Z Y : Type*}
    [Fintype E] [Fintype Z] [Fintype Y]
    (T : E → Z → Y → ℝ) (π : Z → Y → ℝ) (πZ : Z → ℝ) (w : E → ℝ)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (hw : ∀ e, 0 ≤ w e)
    (hT : ∀ e z y, 0 ≤ T e z y) (hπ : ∀ z y, 0 ≤ π z y) (hπZ : ∀ z, 0 ≤ πZ z)
    (hOld : ∀ e z y, T e z y ≤ R * w e * πZ z)
    (hmarginal : ∀ z y, (∑ e, T e z y) ≤ π z y) (K : ℕ)
    (hK : ∀ z, (Finset.univ.filter (fun y => 0 < π z y)).card ≤ K) :
    ∃ good : E → Z → Y → ℝ,
      (∀ e z y, 0 ≤ good e z y ∧ good e z y ≤ T e z y) ∧
      (∑ e, ∑ z, ∑ y, (T e z y - good e z y)) ≤ ε * (K : ℝ) * ∑ z, πZ z ∧
      ∀ e y, (∑ z, good e z y) ≤ (R / ε) * w e * ∑ z, π z y := by
  refine ⟨paletteRefinementRetained T π πZ ε,
    paletteRefinementRetained_bounds T π πZ ε hT, ?_, ?_⟩
  · exact paletteRefinement_lost_mass T π πZ hε hπZ hmarginal K hK
  · exact paletteRefinement_joint_cap T π πZ w hε hR hw hπ hOld

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
