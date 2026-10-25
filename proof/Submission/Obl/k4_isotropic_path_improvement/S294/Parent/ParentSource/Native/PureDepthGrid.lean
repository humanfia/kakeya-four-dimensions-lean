-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PureDepthGrid, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PureDepthGrid.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PureDepthGrid.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PureDepthGrid.lean.
-- Existing source attributions are preserved below.

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Fixed finite lower test depths approximate every actual depth with
an arbitrarily small additive error, independently of the path tolerance. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

theorem exists_fixed_lower_depth_grid {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ depths : Fin (n + 1) → ℝ,
      (∀ i, 0 ≤ depths i ∧ depths i ≤ L) ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ L → ∃ i, depths i ≤ r ∧ r - depths i ≤ ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (L / ε)
  have hnpos : 0 < (n : ℝ) := (div_pos hL hε).trans hn
  have hnn : 0 < n := Nat.cast_pos.mp hnpos
  have hstep : L / n < ε := (div_lt_iff₀ hnpos).mpr (by
    have h := (div_lt_iff₀ hε).mp hn
    nlinarith)
  let depths : Fin (n + 1) → ℝ := fun i => L * (i : ℝ) / n
  have hdepths (i : Fin (n + 1)) : 0 ≤ depths i ∧ depths i ≤ L := by
    have hi : (i : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    dsimp only [depths]
    constructor
    · positivity
    · exact (div_le_iff₀ hnpos).mpr (mul_le_mul_of_nonneg_left hi hL.le)
  refine ⟨n, hnn, depths, hdepths, ?_⟩
  intro r hr hrL
  let t := n * r / L
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have htmax : t ≤ (n : ℝ) := by
    dsimp only [t]
    exact (div_le_iff₀ hL).mpr (mul_le_mul_of_nonneg_left hrL hnpos.le)
  have hfloor : ⌊t⌋₊ ≤ n := Nat.floor_le_of_le htmax
  let i : Fin (n + 1) := ⟨⌊t⌋₊, Nat.lt_succ_of_le hfloor⟩
  refine ⟨i, ?_, ?_⟩
  · have h := Nat.floor_le ht
    change L * (⌊t⌋₊ : ℝ) / n ≤ r
    apply (div_le_iff₀ hnpos).mpr
    have ht' : L * t = (n : ℝ) * r := by dsimp only [t]; field_simp
    nlinarith
  · have h := Nat.lt_floor_add_one t
    change r - L * (⌊t⌋₊ : ℝ) / n ≤ ε
    have hnear : r - L * (⌊t⌋₊ : ℝ) / n < L / n := by
      apply (lt_div_iff₀ hnpos).mpr
      have ht' : L * t = (n : ℝ) * r := by dsimp only [t]; field_simp
      have heq : (r - L * (⌊t⌋₊ : ℝ) / n) * n = r * n - L * ⌊t⌋₊ := by field_simp
      rw [heq]
      nlinarith
    exact hnear.le.trans hstep.le

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
