-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_depth_step.GridShading.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Basic
import Submission.WZ.Obl.wz_tower_depth_step.TubeVolume
import Submission.WZ.Obl.wz_nonflat_factored_improvement.GridUnion

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_depth_step

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridKey gridCell gridUnion)

/-- A bounded set meets only finitely many cells of a fixed grid. -/
lemma bounded_grid_keys {S : Set Space} (hS : Bornology.IsBounded S) {b : ℝ} (hb : 0 < b) :
    ∃ K : Finset (Fin 3 → ℤ), ∀ p ∈ S, gridKey b p ∈ K := by
  obtain ⟨R, hR⟩ := hS.subset_ball (0 : Space)
  refine ⟨Finset.Icc (fun _ => ⌊-R / b⌋) (fun _ => ⌊R / b⌋), ?_⟩
  intro p hp
  have hpR : ‖p‖ < R := by simpa only [mem_ball, dist_zero_right] using hR hp
  have hcoord (i : Fin 3) : -R ≤ p i ∧ p i ≤ R := by
    have h := (PiLp.norm_apply_le p i).trans hpR.le
    simpa only [Real.norm_eq_abs, abs_le] using h
  apply Finset.mem_Icc.mpr
  constructor <;> intro i
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right hb).mpr (hcoord i).1)
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right hb).mpr (hcoord i).2)

/-- Cells of side at most r that meet an r-tube lie in the tube of radius 3r. -/
lemma gridUnion_tube_subset {r b : ℝ} (hb : 0 < b) (hbr : b ≤ r)
    {x v : Space} (s : Finset (Fin 3 → ℤ))
    (hs : ∀ z ∈ s, (Tube r x v ∩ gridCell b z).Nonempty) :
    gridUnion b s ⊆ Tube (3 * r) x v := by
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
  have hh := WangZahlLot.Obl.wz_nonflat_factored_improvement.gridCell_subset_neighborhood hb (hs z hz) hpz
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hh
  obtain ⟨a, ha, hqa⟩ := mem_thickening_iff.mp hq
  apply mem_thickening_iff.mpr
  refine ⟨a, ha, ?_⟩
  have ht := dist_triangle p q a
  linarith

lemma gridUnion_tube_volume {r b : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : 0 < b) (hbr : b ≤ r) {x v : Space} (hv : ‖v‖ = 1)
    (s : Finset (Fin 3 → ℤ)) (hs : ∀ z ∈ s, (Tube r x v ∩ gridCell b z).Nonempty) :
    volume (gridUnion b s) ≤ ENNReal.ofReal (10368 * r ^ 2) := by
  calc
    _ ≤ volume (Tube (3 * r) x v) := measure_mono (gridUnion_tube_subset hb hbr s hs)
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ 3) * volume (Tube r x v) := tube_volume_enlarge hr (by norm_num) x v
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ 3) * ENNReal.ofReal (384 * r ^ 2) :=
      mul_le_mul' le_rfl (WangZahlLot.Obl.wz_affine_packet_counting_transfer.tube_volume_upper hr hr1 x v hv)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-- Fine shading mass forces a coarse union of grid cells to have substantial density. -/
theorem grid_shading_density {δ b d : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    {n : ℕ} (hn : 0 < n) {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (s : Finset (Fin 3 → ℤ))
    (hmass : d * n * δ ^ 2 ≤ ∑ i, volume.real (Y i ∩ gridUnion b s)) :
    d / 16 * b ^ 2 ≤ volume.real (gridUnion b s) := by
  have hbound : (∑ i, volume.real (Y i ∩ gridUnion b s)) ≤
      (n : ℝ) * (16 * δ ^ 2 / b ^ 2 * volume.real (gridUnion b s)) := by
    calc
      _ ≤ ∑ i : Fin n, volume.real (Tube δ (x i) (v i) ∩ gridUnion b s) :=
        Finset.sum_le_sum (fun i _ => measureReal_mono (Set.inter_subset_inter_left _ (hY i))
          (ne_top_of_le_ne_top (WangZahlLot.Obl.wz_nonflat_factored_improvement.gridUnion_volume_ne_top hb s)
            (measure_mono inter_subset_right)))
      _ ≤ ∑ _i : Fin n, 16 * δ ^ 2 / b ^ 2 * volume.real (gridUnion b s) :=
        Finset.sum_le_sum (fun i _ =>
          WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_gridUnion_volumeReal hb δ (x i) (v i) (hv i) s)
      _ = _ := by simp
  have hmul := hmass.trans hbound
  have hcancel : d ≤ 16 / b ^ 2 * volume.real (gridUnion b s) := by
    apply (mul_le_mul_iff_left₀ (show 0 < (n : ℝ) * δ ^ 2 by positivity)).mp
    convert hmul using 1 <;> ring
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hh := mul_le_mul_of_nonneg_right hcancel hb2.le
  field_simp at hh
  linarith

end WangZahlLot.Obl.wz_tower_depth_step
