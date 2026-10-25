-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.TubeRegularity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/- Adapted from session x0449 on o152 in this workspace. -/
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_tower_convex_count_composition.Geometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularPruning

/-! Local regularity of a tube shading at one prescribed scale. -/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- Half of any tube shading can be retained so that every remaining point sees
an `r/32` fraction of the original mass within radius `r`.
This is the one-scale regularization used in the local lengthening construction. -/
theorem regular_tube_shading_at_scale {δ r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hδr : δ ≤ r / 8) {x v : Space} (hv : ‖v‖ = 1) {Y : Set Space}
    (hY : MeasurableSet Y) (hYT : Y ⊆ T δ x v) :
    ∃ Z : Set Space, MeasurableSet Z ∧ Z ⊆ Y ∧
      (1 / 2 : ℝ≥0∞) * volume Y ≤ volume Z ∧
      ∀ p ∈ Z, ENNReal.ofReal (r / 32) * volume Y ≤ volume (Z ∩ ball p r) := by
  classical
  obtain ⟨K, hK, hcover⟩ :=
    WangZahlLot.Obl.wz_tower_convex_count_composition.tube_ball_cover
      (r := r / 8) (by positivity) (by linarith) x v hv
  let C : ℕ → Set Space := fun k => ball (x + ((k : ℝ) * (r / 8)) • v) (r / 2)
  have hCm : ∀ k, MeasurableSet (C k) := fun _ => measurableSet_ball
  have hYfin : volume Y ≠ ∞ :=
    measure_ne_top_of_subset hYT
      ((isBounded_closedBall.subset (segment_subset_closedBall_left x (x + v))).thickening.measure_lt_top).ne
  have hcoeff : (K : ℝ≥0∞) * ENNReal.ofReal (r / 32) ≤ 1 / 2 := by
    calc (K : ℝ≥0∞) * ENNReal.ofReal (r / 32)
        = ENNReal.ofReal ((K : ℝ) * (r / 32)) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg K)]
          simp
      _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  have hbudget : (∑ _k ∈ Finset.range K, ENNReal.ofReal (r / 32) * volume Y) ≤
      (1 / 2 : ℝ≥0∞) * volume Y := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc] using
      mul_le_mul_left hcoeff (volume Y)
  obtain ⟨Z, hZ, hZY, hmass, hreg⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.regular_subshading_half volume
      (Finset.range K) C (fun _ => ENNReal.ofReal (r / 32) * volume Y)
      (fun k _ => hCm k) Y hY hYfin hbudget
  refine ⟨Z, hZ, hZY, hmass, ?_⟩
  intro p hp
  have hpT : p ∈ T (r / 8) x v :=
    thickening_mono hδr _ (hYT (hZY hp))
  obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp (hcover hpT)
  have hpC : p ∈ C k := by
    simpa only [C, show 4 * (r / 8) = r / 2 by ring] using hpk
  have hnon : (Z ∩ C k).Nonempty := ⟨p, hp, hpC⟩
  have hlocal := ((hreg k hk).resolve_left hnon.ne_empty).le
  refine hlocal.trans (measure_mono (inter_subset_inter_right Z ?_))
  intro q hq
  change dist q (x + ((k : ℝ) * (r / 8)) • v) < r / 2 at hq
  change dist p (x + ((k : ℝ) * (r / 8)) • v) < r / 2 at hpC
  rw [mem_ball]
  calc dist q p ≤ dist q (x + ((k : ℝ) * (r / 8)) • v) +
      dist (x + ((k : ℝ) * (r / 8)) • v) p := dist_triangle _ _ _
    _ < r := by rw [dist_comm _ p]; linarith

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
