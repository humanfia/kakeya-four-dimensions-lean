-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.PolySelect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.PolyExtension
import Submission.WZ.Obl.wz_compact_offset_normalization.Select

/-!
# Conflicts between the new tubes have polynomially bounded degree

Two new tubes are in conflict when they meet in volume more than `δ² / 2`. By the crossing
lemma of `wz_compact_offset_normalization`, all tubes in conflict with a given one come from
old tubes inside the preimage under `pshear c` of a set of volume `10¹¹ δ²`, whose volume is
`10¹⁷ (1 + |c|)² δ²`; the container count bounds their number by `10⁴⁰ (1 + |c|)⁴`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_compact_offset_normalization (Space Tube crossing extSeg
  extSeg_thickening_volume count_in_container)

/-- The degree bound of the conflict graph of the new tubes. -/
noncomputable def pdegreeBound (c : ℝ) : ℕ := ⌈(10 : ℝ) ^ 40 * (1 + |c|) ^ 4⌉₊

theorem pdegreeBound_le (c : ℝ) :
    (pdegreeBound c : ℝ) ≤ 10 ^ 40 * (1 + |c|) ^ 4 + 1 := by
  unfold pdegreeBound
  have := abs_nonneg c
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem psa_sq_inv (c : ℝ) : (psa c ^ 2)⁻¹ = 10 ^ 6 * (1 + |c|) ^ 2 := by
  unfold psa
  have : 0 < 1 + |c| := by have := abs_nonneg c; linarith
  field_simp
  ring

open Classical in
theorem pconflict_degree {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10000) (c : ℝ)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i, 1 / 2 ≤ v i 2)
    (hover : ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i))) (i : Fin n) :
    (Finset.univ.filter (fun k => ENNReal.ofReal (δ ^ 2 / 2) <
      volume (Tube δ (pnewBase c (x i) (v i)) (pnewDir c (v i)) ∩
        Tube δ (pnewBase c (x k) (v k)) (pnewDir c (v k))))).card ≤ pdegreeBound c := by
  set W := pshear c ⁻¹' thickening (5000 * δ) (extSeg (pnewBase c (x i) (v i))
    (pnewDir c (v i))) with hWdef
  have hsub : (Finset.univ.filter (fun k => ENNReal.ofReal (δ ^ 2 / 2) <
      volume (Tube δ (pnewBase c (x i) (v i)) (pnewDir c (v i)) ∩
        Tube δ (pnewBase c (x k) (v k)) (pnewDir c (v k))))) ⊆
      Finset.univ.filter (fun k => Tube δ (x k) (v k) ⊆ W) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have hcross := crossing hδ hδ1 (pnewDir_norm (hv2 i)) (pnewDir_norm (hv2 k)) hk.2
    intro p hp
    exact hcross (pshear_image_tube_subset_new c δ (hv k) (hv2 k) ⟨p, hp, rfl⟩)
  have hm : 0 ≤ 1 + |c| := by have := abs_nonneg c; linarith
  have hWvol : volume W ≤ ENNReal.ofReal ((10 ^ 17 * (1 + |c|) ^ 2) * δ ^ 2) := by
    rw [hWdef, pshear_volume_preimage]
    calc ENNReal.ofReal ((psa c ^ 2)⁻¹) *
          volume (thickening (5000 * δ) (extSeg (pnewBase c (x i) (v i)) (pnewDir c (v i))))
        ≤ ENNReal.ofReal ((psa c ^ 2)⁻¹) * ENNReal.ofReal (10 ^ 11 * δ ^ 2) := by
          gcongr
          exact extSeg_thickening_volume hδ hδ1 _ _ (pnewDir_norm (hv2 i))
      _ = ENNReal.ofReal ((10 ^ 17 * (1 + |c|) ^ 2) * δ ^ 2) := by
          rw [← ENNReal.ofReal_mul (by have := psa_pos c; positivity), psa_sq_inv]
          congr 1
          ring
  have hcount := count_in_container hδ x v hv hover (by positivity) hWvol
  have hle := Finset.card_le_card hsub
  have h2 : ((Finset.univ.filter (fun k => Tube δ (x k) (v k) ⊆ W)).card : ℝ) ≤
      (pdegreeBound c : ℝ) := by
    refine hcount.trans ?_
    unfold pdegreeBound
    refine le_trans (le_of_eq ?_) (Nat.le_ceil _)
    ring
  exact hle.trans (by exact_mod_cast h2)

end WangZahlLot.Obl.wz_intermediate_twist_normalization
