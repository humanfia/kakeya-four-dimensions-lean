-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_brush_selection.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

namespace WangZahlLot.Obl.wz_transverse_brush_selection

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- The overlap of two transverse unit tubes has volume at most `4096 δ³ / b`. -/
theorem transverse_intersection_volume {δ b : ℝ} (hδ : 0 < δ)
    (hb : 0 < b) (hb1 : b ≤ 1) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hsep : b ≤ min ‖v - w‖ ‖v + w‖) :
    volume (thickening δ (segment ℝ x (x + v)) ∩
      thickening δ (segment ℝ y (y + w))) ≤ ENNReal.ofReal (4096 * δ ^ 3 / b) := by
  let T : Set ℝ := {t | t ∈ Icc 0 1 ∧
    x + t • v ∈ thickening (2 * δ) (segment ℝ y (y + w))}
  have hdiam : ∀ s ∈ T, ∀ t ∈ T, dist s t ≤ 8 * δ / b := by
    intro s hs t ht
    obtain ⟨p, hp, hsp⟩ := mem_thickening_iff.mp hs.2
    obtain ⟨q, hq, htq⟩ := mem_thickening_iff.mp ht.2
    rw [segment_eq_image'] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨c, hc, rfl⟩ := hq
    simp only [add_sub_cancel_left, dist_eq_norm] at hsp htq
    have hd : ‖(s - t) • v - (a - c) • w‖ < 4 * δ := by
      have heq : (s - t) • v - (a - c) • w =
          (x + s • v - (y + a • w)) - (x + t • v - (y + c • w)) := by module
      rw [heq]
      exact (norm_sub_le _ _).trans_lt (by linarith)
    have h := WangZahlLot.Obl.wz_direction_density_transfer.scale_sep
      (a := s - t) (b := a - c) hv hw (le_min_iff.mp hsep).1 (le_min_iff.mp hsep).2
    rw [Real.dist_eq, le_div_iff₀ hb]
    nlinarith
  have hsub : thickening δ (segment ℝ x (x + v)) ∩
      thickening δ (segment ℝ y (y + w)) ⊆
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
    have := dist_triangle (x + t • v) p z
    rw [dist_comm (x + t • v) p] at this
    linarith
  calc
    _ ≤ volume (thickening δ ((fun t : ℝ => x + t • v) '' T)) := measure_mono hsub
    _ ≤ ENNReal.ofReal (128 * (2 * (8 * δ / b) + δ) * δ ^ 2) :=
      WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
        x v hv (fun _ ht => ht.1) hδ (by positivity) hdiam
    _ ≤ ENNReal.ofReal (4096 * δ ^ 3 / b) := by
      apply ENNReal.ofReal_le_ofReal
      apply (le_div_iff₀ hb).2
      have heq : 128 * (2 * (8 * δ / b) + δ) * δ ^ 2 * b =
          128 * (16 + b) * δ ^ 3 := by field_simp; ring
      rw [heq]
      have hδ3 : 0 ≤ δ ^ 3 := by positivity
      nlinarith

end WangZahlLot.Obl.wz_transverse_brush_selection
