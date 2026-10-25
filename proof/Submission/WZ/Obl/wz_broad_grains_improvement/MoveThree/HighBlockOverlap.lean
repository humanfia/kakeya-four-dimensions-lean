-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.HighBlockOverlap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/HighBlockOverlap.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit be976b9, HighBlockOverlap.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (bodyCount bodyCount_inter measurable_bodyCount body_mass_le_mul_of_count half_mass_after_loss)

/-- A container with sufficiently small volume supports a half-mass common
cut on which the original and retained overlap both exceed `M`. -/
theorem high_block_overlap {L : ℕ} (H : Fin L → Set V) (U : Set V) {M : ℝ}
    (hM : 0 ≤ M) (hHm : ∀ j, MeasurableSet (H j)) (hUm : MeasurableSet U)
    (hsub : ∀ j, H j ⊆ U) (hfin : (∑ j, μ (H j)) ≠ ⊤)
    (hbudget : O M * μ U ≤ (1 / 2 : ENNReal) * ∑ j, μ (H j)) :
    ∃ D : Set V, MeasurableSet D ∧
      (1 / 2 : ENNReal) * ∑ j, μ (H j) ≤ ∑ j, μ (H j ∩ D) ∧
      ∀ p ∈ ⋃ j, H j ∩ D,
        M < q L {j | p ∈ H j ∩ D} ∧ M < q L {j | p ∈ H j} := by
  classical
  let D := {p | M < bodyCount H p}
  have hD : MeasurableSet D := measurableSet_lt measurable_const (measurable_bodyCount hHm)
  let W := fun j => H j \ D
  have hWm (j) : MeasurableSet (W j) := (hHm j).diff hD
  have hloss : (∑ j, μ (W j)) ≤ O M * μ U := by
    have Hcount (p : V) : bodyCount W p ≤ M * bodyCount (fun _ : Fin 1 => U) p := by
      by_cases hpU : p ∈ U
      · have hsingle : bodyCount (fun _ : Fin 1 => U) p = 1 := by simp [bodyCount, hpU]
        rw [hsingle, mul_one]
        change bodyCount (fun j => H j \ D) p ≤ M
        rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount_diff]
        by_cases hpD : p ∈ D
        · simpa only [ite_eq_left hpD] using hM
        · simpa only [ite_eq_right hpD] using le_of_not_gt hpD
      · have hnone (j : Fin L) : p ∉ W j := fun hp => hpU (hsub j hp.1)
        simp only [bodyCount, hnone, not_false_eq_true, Set.setOf_false, Set.ncard_empty,
          Nat.cast_zero]
        positivity
    have HH := body_mass_le_mul_of_count hWm (fun _ : Fin 1 => hUm) hM Hcount
    simpa only [Fin.sum_univ_one] using HH
  have hsplit : (∑ j, μ (H j)) = (∑ j, μ (H j ∩ D)) + ∑ j, μ (W j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => (measure_inter_add_sdiff (H j) hD).symm)
  refine ⟨D, hD, half_mass_after_loss hfin hsplit.le (hloss.trans hbudget), ?_⟩
  intro p hp
  obtain ⟨j, hpj⟩ := mem_iUnion.mp hp
  have hpD : p ∈ D := hpj.2
  have he : bodyCount (fun j => H j ∩ D) p = bodyCount H p := by
    rw [bodyCount_inter, if_pos hpD]
  change M < bodyCount (fun j => H j ∩ D) p ∧ M < bodyCount H p
  exact ⟨he.symm ▸ hpD, hpD⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
