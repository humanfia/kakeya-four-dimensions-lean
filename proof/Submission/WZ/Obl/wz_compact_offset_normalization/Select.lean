-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_compact_offset_normalization.Select.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_compact_offset_normalization.Crossing
import Submission.WZ.Obl.wz_compact_offset_normalization.Extension
import Submission.WZ.Obl.wz_compact_offset_normalization.Greedy
import Submission.WZ.Obl.wz_convex_container_tube_packing

/-!
# Conflicts between the new tubes have bounded degree

Two new tubes are in conflict when they meet in volume more than `δ² / 2`. By the crossing
lemma, all tubes in conflict with a given one come from old tubes inside the preimage of a
set of volume `O(δ²)`, and the packing estimate of `wz_convex_container_tube_packing` bounds
their number by an absolute constant.
-/

namespace WangZahlLot.Obl.wz_compact_offset_normalization

open Set Metric MeasureTheory
open scoped ENNReal

open Classical in
/-- Essentially distinct unit tubes inside a set of volume `V δ²` number at most `10⁶ V²`. -/
theorem count_in_container {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1)
    (hover : ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i)))
    {W : Set Space} {V : ℝ} (hV : 0 ≤ V) (hW : volume W ≤ ENNReal.ofReal (V * δ ^ 2)) :
    ((Finset.univ.filter (fun k => Tube δ (x k) (v k) ⊆ W)).card : ℝ) ≤ 10 ^ 6 * V ^ 2 := by
  set K := Finset.univ.filter (fun k => Tube δ (x k) (v k) ⊆ W) with hK
  let idx : Fin K.card → Fin n := fun j => (K.equivFin.symm j : Fin n)
  have hidx : Function.Injective idx :=
    Subtype.val_injective.comp K.equivFin.symm.injective
  have hmem : ∀ j, idx j ∈ K := fun j => (K.equivFin.symm j).2
  have hWfin : volume W ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW
  have hpack := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hδ
    (fun j => x (idx j)) (fun j => v (idx j)) hWfin (fun j => hv _)
    (fun j => by have := hmem j; rw [hK, Finset.mem_filter] at this; exact this.2)
    (fun j j' hjj' => hover _ _ (hidx.ne hjj'))
  have hbound : ENNReal.ofReal ((K.card : ℝ) * δ ^ 4) ≤
      ENNReal.ofReal (10 ^ 6 * V ^ 2 * δ ^ 4) := by
    refine hpack.trans ?_
    calc ENNReal.ofReal 1000000 * volume W ^ 2
        ≤ ENNReal.ofReal 1000000 * ENNReal.ofReal (V * δ ^ 2) ^ 2 := by gcongr
      _ = ENNReal.ofReal (10 ^ 6 * V ^ 2 * δ ^ 4) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
  have hδ4 : 0 < δ ^ 4 := by positivity
  nlinarith

/-- The degree bound of the conflict graph of the new tubes. -/
noncomputable def degreeBound : ℕ := 10 ^ 40

open Classical in
theorem conflict_degree {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10000) {c : ℝ} (hc : |c| ≤ 100)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i, 1 / 2 ≤ v i 2)
    (hover : ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i))) (i : Fin n) :
    (Finset.univ.filter (fun k => ENNReal.ofReal (δ ^ 2 / 2) <
      volume (Tube δ (newBase c (x i) (v i)) (newDir c (v i)) ∩
        Tube δ (newBase c (x k) (v k)) (newDir c (v k))))).card ≤ degreeBound := by
  set W := shear c ⁻¹' thickening (5000 * δ) (extSeg (newBase c (x i) (v i)) (newDir c (v i)))
    with hWdef
  have hsub : (Finset.univ.filter (fun k => ENNReal.ofReal (δ ^ 2 / 2) <
      volume (Tube δ (newBase c (x i) (v i)) (newDir c (v i)) ∩
        Tube δ (newBase c (x k) (v k)) (newDir c (v k))))) ⊆
      Finset.univ.filter (fun k => Tube δ (x k) (v k) ⊆ W) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have hcross := crossing hδ hδ1 (newDir_norm (hv2 i)) (newDir_norm (hv2 k)) hk.2
    intro p hp
    exact hcross (shear_image_tube_subset_new hc δ (hv k) (hv2 k) ⟨p, hp, rfl⟩)
  have hWvol : volume W ≤ ENNReal.ofReal (10 ^ 17 * δ ^ 2) := by
    rw [hWdef, shear_volume_preimage]
    calc ENNReal.ofReal ((sa ^ 2)⁻¹) *
          volume (thickening (5000 * δ) (extSeg (newBase c (x i) (v i)) (newDir c (v i))))
        ≤ ENNReal.ofReal ((sa ^ 2)⁻¹) * ENNReal.ofReal (10 ^ 11 * δ ^ 2) := by
          gcongr
          exact extSeg_thickening_volume hδ hδ1 _ _ (newDir_norm (hv2 i))
      _ = ENNReal.ofReal (10 ^ 17 * δ ^ 2) := by
          rw [← ENNReal.ofReal_mul (by have := sa_pos; positivity)]
          congr 1
          norm_num [sa]
          ring
  have hcount := count_in_container hδ x v hv hover (by norm_num) hWvol
  have hle := (Finset.card_le_card hsub)
  have : ((Finset.univ.filter (fun k => Tube δ (x k) (v k) ⊆ W)).card : ℝ) ≤ (10 ^ 40 : ℕ) := by
    refine hcount.trans ?_
    norm_num
  rw [degreeBound]
  exact hle.trans (by exact_mod_cast this)

end WangZahlLot.Obl.wz_compact_offset_normalization
