-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.DenseGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CommonCut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Definitions

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal

/-- Removing individually sparse grains loses at most their total density
budget. The surviving sets retain their whole original shading. -/
theorem dense_individual_refinement {L : ℕ} (Y U : Fin L → Set V) {D : ℝ}
    (hYm : ∀ i, MeasurableSet (Y i)) (hfin : (∑ i, volume (Y i)) ≠ ⊤)
    (hbudget : (∑ i, O D * volume (U i)) ≤ (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i)) :
    ∃ W : Fin L → Set V, (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i) ∧
      (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i) ≤ ∑ i, volume (W i) ∧
      ∀ i, W i ≠ ∅ → O D * volume (U i) ≤ volume (W i) := by
  classical
  obtain ⟨good, W, hW, hdense, hloss⟩ :=
    select_dense_packets id Y hYm (fun i => O D * volume (U i))
  refine ⟨W, fun i => ⟨(hW i).1, (hW i).2.1⟩, half_mass_after_loss hfin hloss hbudget, ?_⟩
  intro i hi
  have higood : i ∈ good := by
    by_contra h
    exact hi ((hW i).2.2 h)
  simpa only [id_eq, Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton] using
    hdense i higood

/-- A common cut retaining fine incidence mass, followed by individual
density selection, retains a fixed share of the original grain mass. -/
theorem common_cut_dense_grains {n N L : ℕ} (f : Fin n → Fin N) (γ : Fin L → Fin N)
    (Z : Fin n → Set V) (H U : Fin L → Set V) (C : Fin N → Set V) {m t D : ℝ}
    (hm : 0 < m) (ht : 0 ≤ t)
    (hZm : ∀ i, MeasurableSet (Z i)) (hHm : ∀ j, MeasurableSet (H j))
    (hCm : ∀ k, MeasurableSet (C k)) (hfin : (∑ j, volume (H j)) ≠ ⊤)
    (hdisj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H i) (H j))
    (heq : ∀ k, assignedFiber γ H k = assignedFiber f Z k)
    (hlevel : ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m)
    (hretain : O t * ∑ i, volume (Z i) ≤ ∑ i, volume (Z i ∩ C (f i)))
    (hbudget : (∑ j, O D * volume (U j)) ≤ O (t / 4) * ∑ j, volume (H j)) :
    ∃ W : Fin L → Set V, (∀ j, MeasurableSet (W j) ∧ W j ⊆ H j ∩ C (γ j)) ∧
      O (t / 4) * ∑ j, volume (H j) ≤ ∑ j, volume (W j) ∧
      ∀ j, W j ≠ ∅ → O D * volume (U j) ≤ volume (W j) := by
  have hcut := common_cut_retains_grain_mass f γ Z H C hm ht hZm hHm hCm hdisj heq hlevel hretain
  have hhalf : (1 / 2 : ℝ≥0∞) * O (t / 2) = O (t / 4) := by
    have he : (1 / 2 : ℝ≥0∞) = O (1 / 2 : ℝ) := by norm_num [O, ENNReal.ofReal_div_of_pos]
    rw [he, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  have hbound : O (t / 4) * ∑ j, volume (H j) ≤
      (1 / 2 : ℝ≥0∞) * ∑ j, volume (H j ∩ C (γ j)) := by
    rw [← hhalf, mul_assoc]
    exact mul_le_mul' le_rfl hcut
  have hcutfin : (∑ j, volume (H j ∩ C (γ j))) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (Finset.sum_le_sum fun _ _ => measure_mono inter_subset_left)
  obtain ⟨W, hW, hmass, hdense⟩ := dense_individual_refinement (fun j => H j ∩ C (γ j)) U
    (fun j => (hHm j).inter (hCm (γ j))) hcutfin (hbudget.trans hbound)
  exact ⟨W, hW, hbound.trans hmass, hdense⟩

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
