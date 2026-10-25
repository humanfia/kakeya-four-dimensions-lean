-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.UnitCarrier.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs
import Submission.WZ.Obl.wz_compact_offset_normalization.Basic

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set Metric

/-- A tube of radius one with unit direction cannot fit in the unit ball. -/
theorem unit_tube_not_subset_ball (y w : V) (hw : ‖w‖ = 1) : ¬ T 1 y w ⊆ I := by
  intro h
  have hseg := WangZahlLot.Obl.wz_compact_offset_normalization.segment_subset_of_tube
    (by norm_num : (0 : ℝ) < 1) h
  have hy : y = 0 := by simpa using hseg (left_mem_segment ℝ y (y + w))
  have hyw : y + w = 0 := by simpa using hseg (right_mem_segment ℝ y (y + w))
  have hw0 : w = 0 := by simpa only [hy, zero_add] using hyw
  simp only [hw0, norm_zero, zero_ne_one] at hw

/-- The frozen slab count at radius one holds for every family of unit
directions: no member is contained in the ambient unit ball. -/
theorem unit_radius_frostman {N : ℕ} (y w : Fin N → V) (hw : ∀ k, ‖w k‖ = 1)
    (l : ℝ) : F 1 l N y w := by
  intro u t r _ _
  have he : {k | T 1 (y k) (w k) ⊆ I ∩ Q u t r} = (∅ : Set (Fin N)) := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hk
    exact unit_tube_not_subset_ball (y k) (w k) (hw k) (hk.trans inter_subset_left)
  simp only [he, q, Set.ncard_empty, Nat.cast_zero, O, ENNReal.ofReal_zero]
  exact zero_le

end WangZahlLot.Obl.wz_coarse_grains_assembly
