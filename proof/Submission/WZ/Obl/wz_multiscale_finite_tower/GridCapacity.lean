-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.GridCapacity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.CellClasses

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (gridCell gridUnion gridKeys gridKey gridKey_mem mem_gridCell_key gridCell_dist_lt
    gridUnion_volumeReal gridUnion_volume_ne_top)
open WangZahlLot.Obl.wz_flat_factored_improvement (gridHull)

lemma gridHull_ball_subset {a R : ℝ} (ha : 0 < a) (S : Finset (Fin 3 → ℤ))
    (x : Space) : gridHull a S (ball x R) ⊆ ball x (R + 2 * a) := by
  classical
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
  obtain ⟨q, hq, hqz⟩ := (Finset.mem_filter.mp hz).2
  have hpq := gridCell_dist_lt ha hpz hqz
  exact mem_ball.mpr ((dist_triangle p q x).trans_lt (by linarith [mem_ball.mp hq]))

lemma gridHull_tube_subset {a r : ℝ} (ha : 0 < a) (S : Finset (Fin 3 → ℤ))
    (x v : Space) : gridHull a S (Tube r x v) ⊆ Tube (r + 2 * a) x v := by
  classical
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
  obtain ⟨q, hq, hqz⟩ := (Finset.mem_filter.mp hz).2
  obtain ⟨u, hu, hqu⟩ := mem_thickening_iff.mp hq
  refine mem_thickening_iff.mpr ⟨u, hu, ?_⟩
  have hpq := gridCell_dist_lt ha hpz hqz
  exact (dist_triangle p q u).trans_lt (by linarith)

/-- Grid shadows of a unit parent tube have uniformly bounded normalized volume. -/
lemma gridHull_tube_volume {a r : ℝ} (ha : 0 < a) (har : 2 * a ≤ r)
    (hr1 : r ≤ 1) (S : Finset (Fin 3 → ℤ)) (x v : Space) (hv : ‖v‖ = 1) :
    volume (gridHull a S (Tube r x v)) ≤ ENNReal.ofReal (256 * r ^ 2) := by
  have hr : 0 < r := (mul_pos (by norm_num) ha).trans_le har
  have hseg : segment ℝ x (x + v) ⊆ segment ℝ x (x + (6 : ℝ) • v) := by
    apply (convex_segment x (x + (6 : ℝ) • v)).segment_subset (left_mem_segment ℝ _ _)
    rw [segment_eq_image']
    refine ⟨1 / 6, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp only [add_sub_cancel_left]
    module
  have hsub : gridHull a S (Tube r x v) ⊆
      WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.Cylinder (2 * r) x v :=
    (gridHull_tube_subset ha S x v).trans
      ((thickening_mono (by linarith) _).trans (thickening_subset_of_subset (2 * r) hseg))
  have hcap := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.cylinder_scaled_volume_le
    hv x (by norm_num : (0 : ℝ) ≤ 2) hr.le hr1
  exact (measure_mono hsub).trans (by norm_num at hcap ⊢; exact hcap)

lemma gridHull_unitBall_volume {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (S : Finset (Fin 3 → ℤ)) :
    volume (gridHull a S (ball (0 : Space) 1)) ≤ ENNReal.ofReal 144 := by
  have hsub : gridHull a S (ball (0 : Space) 1) ⊆ ball 0 3 :=
    (gridHull_ball_subset ha S 0).trans (ball_subset_ball (by linarith))
  apply (measure_mono hsub).trans
  rw [EuclideanSpace.volume_ball_fin_three]
  rw [show (ENNReal.ofReal (3 : ℝ)) ^ 3 = ENNReal.ofReal (27 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 27)]
  exact ENNReal.ofReal_le_ofReal (by linarith [Real.pi_lt_four])

/-- There is a finite grid covering all input shadings, with a capacity independent
of the chosen mesh. -/
lemma unitBall_grid_cover {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ S : Finset (Fin 3 → ℤ), ball (0 : Space) 1 ⊆ gridUnion a S ∧
      (S.card : ℝ) * a ^ 3 ≤ 144 := by
  classical
  let S := (gridKeys a).filter (fun z => (ball (0 : Space) 1 ∩ gridCell a z).Nonempty)
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    refine mem_iUnion₂.mpr ⟨gridKey a p, ?_, mem_gridCell_key ha p⟩
    exact Finset.mem_filter.mpr ⟨gridKey_mem ha ha1 hp, p, hp, mem_gridCell_key ha p⟩
  · have hv : volume (gridUnion a S) ≤ ENNReal.ofReal 144 := gridHull_unitBall_volume ha ha1 _
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
    simpa only [← measureReal_def, gridUnion_volumeReal ha, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 144)] using hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
