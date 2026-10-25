-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.MassPruning, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/MassPruning.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/MassPruning.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/MassPruning.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/MassPruning.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Preparation

/-! Removing light packets by their full original reference mass. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open scoped ENNReal BigOperators

/-- Full-prior reference budgets pay for all light packets together. -/
theorem light_packet_mass_le {ι : Type*} [Fintype ι]
    (weight reference selected : ι → ENNReal) (c : ENNReal)
    (hbudget : ∑ i, weight i * reference i ≤ 1) :
    (∑ i, if c * reference i ≤ selected i then 0 else weight i * selected i) ≤ c := by
  classical
  calc
    _ ≤ ∑ i, c * (weight i * reference i) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact zero_le
      · have hsel : selected i ≤ c * reference i := (lt_of_not_ge hi).le
        calc
          _ ≤ weight i * (c * reference i) := mul_le_mul_of_nonneg_left hsel zero_le
          _ = _ := by ring
    _ = c * ∑ i, weight i * reference i := (Finset.mul_sum _ _ _).symm
    _ ≤ c := by simpa using mul_le_mul_of_nonneg_left hbudget (zero_le : (0 : ENNReal) ≤ c)

/-- Keep all heavy packets, preserving half the original mixture mass. The
floor for each kept packet refers to its full assignment, not its retained part. -/
theorem heavy_packet_mass_ge_half {ι : Type*} [Fintype ι]
    (weight reference selected : ι → ENNReal) {a : ℝ} (ha : 0 ≤ a)
    (hbudget : ∑ i, weight i * reference i ≤ 1)
    (hmass : ENNReal.ofReal a ≤ ∑ i, weight i * selected i) :
    ENNReal.ofReal (a / 2) ≤ ∑ i,
      if ENNReal.ofReal (a / 2) * reference i ≤ selected i then weight i * selected i else 0 := by
  classical
  let c := ENNReal.ofReal (a / 2)
  let good : ι → ENNReal :=
    fun i => if c * reference i ≤ selected i then weight i * selected i else 0
  let bad : ι → ENNReal :=
    fun i => if c * reference i ≤ selected i then 0 else weight i * selected i
  have hsplit : (∑ i, weight i * selected i) = (∑ i, good i) + ∑ i, bad i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [good, bad]
    split_ifs <;> simp
  have hbad : (∑ i, bad i) ≤ c := light_packet_mass_le weight reference selected c hbudget
  have hbound : ENNReal.ofReal a ≤ (∑ i, good i) + c := by
    exact (hmass.trans_eq hsplit).trans (add_le_add le_rfl hbad)
  have hhalf : ENNReal.ofReal a = c + c := by
    dsimp [c]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [hhalf] at hbound
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hbound

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
