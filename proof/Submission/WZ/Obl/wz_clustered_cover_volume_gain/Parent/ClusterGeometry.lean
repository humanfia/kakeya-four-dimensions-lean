-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.ClusterGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.LocalScale
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

abbrev Cylinder := wz_seed_of_balanced_robust_clusters.Cylinder

/-- Nearby directions and one intersection place a whole tube in an enlarged cylinder. -/
theorem aligned_tube_subset_cylinder {δ θ : ℝ} {x v y w : Space}
    (hmeet : (Tube δ x v ∩ Tube δ y w).Nonempty) (hdir : ‖w - v‖ ≤ θ) :
    Tube δ y w ⊆ Cylinder (θ + 3 * δ) (x - (2 : ℝ) • v) v := by
  obtain ⟨p, hp, hp'⟩ := hmeet
  obtain ⟨a, ha, hpa⟩ := mem_thickening_iff.mp hp
  obtain ⟨b, hb, hpb⟩ := mem_thickening_iff.mp hp'
  rw [segment_eq_image'] at ha hb
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  simp only [add_sub_cancel_left] at hpa hpb
  have hbase : ‖(y + t • w) - (x + s • v)‖ < 2 * δ := by
    have hh := dist_triangle (y + t • w) p (x + s • v)
    rw [dist_comm (y + t • w) p] at hh
    rw [← dist_eq_norm]
    linarith
  have hθ : 0 ≤ θ := (norm_nonneg _).trans hdir
  intro q hq
  obtain ⟨b, hb, hqb⟩ := mem_thickening_iff.mp hq
  rw [segment_eq_image'] at hb
  obtain ⟨r, hr, rfl⟩ := hb
  simp only [add_sub_cancel_left] at hqb
  have hrt : |r - t| ≤ 1 := abs_le.mpr ⟨by linarith [hr.1, ht.2], by linarith [hr.2, ht.1]⟩
  apply mem_thickening_iff.mpr
  refine ⟨x + (s + r - t) • v, ?_, ?_⟩
  · rw [segment_eq_image']
    refine ⟨(s + r - t + 2) / 6, ⟨?_, ?_⟩, ?_⟩
    · linarith [hs.1, hr.1, ht.2]
    · linarith [hs.2, hr.2, ht.1]
    · simp only [add_sub_cancel_left]
      module
  · rw [dist_eq_norm]
    have he : q - (x + (s + r - t) • v) =
        (q - (y + r • w)) + ((y + t • w) - (x + s • v)) + (r - t) • (w - v) := by module
    have hlast : ‖(r - t) • (w - v)‖ ≤ θ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul hrt hdir (norm_nonneg _) (by norm_num)).trans_eq (one_mul θ)
    rw [he]
    have htri := norm_add_le (q - (y + r • w)) ((y + t • w) - (x + s • v))
    have htri' := norm_add_le ((q - (y + r • w)) + ((y + t • w) - (x + s • v)))
      ((r - t) • (w - v))
    rw [dist_eq_norm] at hqb
    linarith

theorem tube_reverse (δ : ℝ) (y w : Space) : Tube δ y w = Tube δ (y + w) (-w) := by
  unfold Tube
  rw [show y + w + -w = y by abel, segment_symm]

/-- The preceding containment is invariant under reversal of the line direction. -/
theorem tube_subset_cylinder_of_direction_close {δ θ : ℝ} {x v y w : Space}
    (hmeet : (Tube δ x v ∩ Tube δ y w).Nonempty)
    (hdir : ‖w - v‖ ≤ θ ∨ ‖w + v‖ ≤ θ) :
    Tube δ y w ⊆ Cylinder (θ + 3 * δ) (x - (2 : ℝ) • v) v := by
  rcases hdir with hdir | hdir
  · exact aligned_tube_subset_cylinder hmeet hdir
  · rw [tube_reverse δ y w] at hmeet ⊢
    apply aligned_tube_subset_cylinder hmeet
    simpa only [show -w - v = -(w + v) by abel, norm_neg] using hdir

/-- A pair failing the half-intersection condition lies in a fixed enlarged cylinder. -/
theorem conflicting_tube_subset_cylinder {δ : ℝ} (hδ : 0 < δ)
    {x v y w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hbad : ¬ volume (Tube δ x v ∩ Tube δ y w) ≤
      (1 / 2 : ENNReal) * volume (Tube δ x v)) :
    Tube δ y w ⊆ Cylinder (100003 * δ) (x - (2 : ℝ) • v) v := by
  have hmeet : (Tube δ x v ∩ Tube δ y w).Nonempty :=
    nonempty_of_measure_ne_zero (fun hz => hbad (by rw [hz]; exact bot_le))
  have hdir : ‖w - v‖ ≤ 100000 * δ ∨ ‖w + v‖ ≤ 100000 * δ := by
    by_contra hn
    push Not at hn
    apply hbad
    apply wz_direction_density_transfer.intersection_le_half hδ hv hw
    · simpa [norm_sub_rev] using hn.1.le
    · simpa [add_comm] using hn.2.le
  simpa only [show 100000 * δ + 3 * δ = 100003 * δ by ring] using
    tube_subset_cylinder_of_direction_close hmeet hdir

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
