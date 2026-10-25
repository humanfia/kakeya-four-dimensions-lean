-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_stem_deletion.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

namespace WangZahlLot.Obl.wz_transverse_stem_deletion

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- Two points on a transverse segment that are near a line have nearby parameters. -/
theorem line_parameter_diameter {R b : ℝ} (hb : 0 < b) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hsep : b ≤ min ‖v - w‖ ‖v + w‖) {s t : ℝ}
    (hs : x + s • v ∈ thickening R (range (fun u : ℝ => y + u • w)))
    (ht : x + t • v ∈ thickening R (range (fun u : ℝ => y + u • w))) :
    dist s t ≤ 4 * R / b := by
  obtain ⟨_, ⟨a, rfl⟩, hsa⟩ := mem_thickening_iff.mp hs
  obtain ⟨_, ⟨c, rfl⟩, htc⟩ := mem_thickening_iff.mp ht
  have hd : ‖(s - t) • v - (a - c) • w‖ < 2 * R := by
    have heq : (s - t) • v - (a - c) • w =
        (x + s • v - (y + a • w)) - (x + t • v - (y + c • w)) := by module
    rw [heq]
    simp only [dist_eq_norm] at hsa htc
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hscale := WangZahlLot.Obl.wz_direction_density_transfer.scale_sep
    (a := s - t) (b := a - c) hv hw (hsep.trans (min_le_left _ _))
      (hsep.trans (min_le_right _ _))
  rw [Real.dist_eq, le_div_iff₀ hb]
  nlinarith

/-- An unequal-radius tube/line intersection is bounded by the length of the
portion of the segment near the line, times the squared tube radius. -/
theorem tube_line_intersection_volume_le {δ r b : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hb : 0 < b) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hsep : b ≤ min ‖v - w‖ ‖v + w‖) :
    volume (thickening δ (segment ℝ x (x + v)) ∩
      thickening r (range (fun t : ℝ => y + t • w))) ≤
      ENNReal.ofReal (128 * (8 * (δ + r) / b + δ) * δ ^ 2) := by
  let T : Set ℝ := {t | t ∈ Icc 0 1 ∧
    x + t • v ∈ thickening (δ + r) (range (fun u : ℝ => y + u • w))}
  have hT : T ⊆ Icc 0 1 := fun _ ht => ht.1
  have hdiam : ∀ s ∈ T, ∀ t ∈ T, dist s t ≤ 4 * (δ + r) / b :=
    fun _ hs _ ht => line_parameter_diameter hb hv hw hsep hs.2 ht.2
  have hsub : thickening δ (segment ℝ x (x + v)) ∩
      thickening r (range (fun t : ℝ => y + t • w)) ⊆
      thickening δ ((fun t : ℝ => x + t • v) '' T) := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp.1
    obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp.2
    rw [segment_eq_image'] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    simp only [add_sub_cancel_left] at hpq
    apply mem_thickening_iff.mpr
    refine ⟨x + t • v, ⟨t, ⟨ht, ?_⟩, rfl⟩, hpq⟩
    apply mem_thickening_iff.mpr
    refine ⟨z, hz, ?_⟩
    have htri := dist_triangle (x + t • v) p z
    rw [dist_comm (x + t • v) p] at htri
    linarith
  calc
    _ ≤ volume (thickening δ ((fun t : ℝ => x + t • v) '' T)) := measure_mono hsub
    _ ≤ ENNReal.ofReal (128 * (2 * (4 * (δ + r) / b) + δ) * δ ^ 2) :=
      WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
        x v hv hT hδ (by positivity) hdiam
    _ = _ := by congr 1; ring

end WangZahlLot.Obl.wz_transverse_stem_deletion
