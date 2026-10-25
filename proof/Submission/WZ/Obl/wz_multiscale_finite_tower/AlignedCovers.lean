-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.AlignedCovers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedAxes

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (doubled centered_segment)

def axisLine (x v : Space) : Set Space := Set.range (fun t : ℝ => axisMidpoint x v + t • v)

lemma axis_line_param {r : ℝ} {x v p : Space} (hp : p ∈ thickening r (axisLine x v)) :
    ∃ a : ℝ, ‖p - (axisMidpoint x v + a • v)‖ < r := by
  obtain ⟨q, ⟨a, rfl⟩, hq⟩ := mem_thickening_iff.mp hp
  exact ⟨a, by simpa only [dist_eq_norm] using hq⟩

lemma axis_line_angle {s r : ℝ} (hs : 0 < s) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : Tube s x v ⊆ thickening r (axisLine y w)) :
    min ‖v - w‖ ‖v + w‖ ≤ 4 * r := by
  obtain ⟨a, ha⟩ := axis_line_param
    (hT (self_subset_thickening hs _ (left_mem_segment ℝ _ _)))
  obtain ⟨b, hb⟩ := axis_line_param
    (hT (self_subset_thickening hs _ (right_mem_segment ℝ _ _)))
  have he : v - (b - a) • w =
      (x + v - (axisMidpoint y w + b • w)) - (x - (axisMidpoint y w + a • w)) := by module
  have hc : ‖v - (b - a) • w‖ < 2 * r := by
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  exact (unit_near_multiple hv hw (b - a)).trans (by linarith)

/-- Under scalar alignment, line containment already gives an exact unit cover. -/
theorem aligned_line_to_unit {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hr : r ≤ 1 / 8)
    {x v y w u : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvu : ‖v - u‖ ≤ 1 / 10) (hwu : ‖w - u‖ ≤ 1 / 10)
    (hmid : ‖axisMidpoint x v‖ ≤ 1)
    (halign : inner ℝ v (axisMidpoint x v) = inner ℝ w (axisMidpoint y w))
    (hT : Tube s x v ⊆ thickening r (axisLine y w)) :
    Tube s x v ⊆ Tube (16 * r) y w := by
  have hr0 := hs.trans_le hsr
  have hvw : ‖v - w‖ ≤ 4 * r := by
    rcases min_le_iff.mp (axis_line_angle hs hv hw hT) with hh | hh
    · exact hh
    · have hh' := norm_add_lower_of_common_direction hv hvu hwu
      linarith
  have hmidmem : axisMidpoint x v ∈ Tube s x v := self_subset_thickening hs _
    (by simpa only [axisMidpoint, zero_smul, add_zero] using
      centered_segment x v (a := 0) (by norm_num))
  obtain ⟨a, ha⟩ := axis_line_param (hT hmidmem)
  have ha' : ‖axisMidpoint x v - axisMidpoint y w - a • w‖ < r := by
    simpa only [sub_add_eq_sub_sub] using ha
  have hcenters : ‖axisMidpoint x v - axisMidpoint y w‖ < 6 * r := by
    have hh := aligned_midpoint_distance hw halign a
    have hh' := mul_le_mul hvw hmid (norm_nonneg _) (by positivity : 0 ≤ 4 * r)
    linarith
  intro p hp
  obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  have habs : |t - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine mem_thickening_iff.mpr ⟨axisMidpoint y w + (t - 1 / 2) • w,
    centered_segment y w habs, ?_⟩
  rw [dist_eq_norm]
  have he : p - (axisMidpoint y w + (t - 1 / 2) • w) =
      (p - (x + t • v)) + (axisMidpoint x v - axisMidpoint y w) +
        (t - 1 / 2) • (v - w) := by dsimp [axisMidpoint]; module
  rw [he]
  have hlast : ‖(t - 1 / 2) • (v - w)‖ ≤ 2 * r := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul habs hvw (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  calc
    _ ≤ (‖p - (x + t • v)‖ + ‖axisMidpoint x v - axisMidpoint y w‖) +
        ‖(t - 1 / 2) • (v - w)‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < 16 * r := by linarith

/-- A child axis can serve as the axis of the entire old doubled cover, with a
bounded longitudinal parameter and a constant transverse error. -/
lemma doubled_cover_representative {s r : ℝ} (hs : 0 < s) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : Tube s x v ⊆ doubled r y w) :
    ∀ p ∈ doubled r y w, ∃ a : ℝ, |a| ≤ 2 ∧
      ‖p - (axisMidpoint x v + a • v)‖ < 20 * r := by
  have hangle := doubled_axis_angle hs hv hw hT
  have hangle' : min ‖w - v‖ ‖w + v‖ ≤ 8 * r := by
    simpa only [norm_sub_rev w v, add_comm w v] using hangle
  obtain ⟨b, hb, hwv⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_sign hangle'
  have hmidmem : axisMidpoint x v ∈ Tube s x v := self_subset_thickening hs _
    (by simpa only [axisMidpoint, zero_smul, add_zero] using
      centered_segment x v (a := 0) (by norm_num))
  obtain ⟨c, hc, hmc⟩ := mem_doubled_axis_param (hT hmidmem)
  intro p hp
  obtain ⟨a, ha, hpa⟩ := mem_doubled_axis_param hp
  have hac : |a - c| ≤ 2 := (abs_sub a c).trans (by linarith)
  refine ⟨(a - c) * b, ?_, ?_⟩
  · rw [abs_mul]
    simpa using mul_le_mul hac hb (abs_nonneg b) (by norm_num : (0 : ℝ) ≤ 2)
  have he : p - (axisMidpoint x v + ((a - c) * b) • v) =
      (p - (axisMidpoint y w + a • w)) -
      (axisMidpoint x v - (axisMidpoint y w + c • w)) + (a - c) • (w - b • v) := by module
  rw [he]
  have hlast : ‖(a - c) • (w - b • v)‖ ≤ 16 * r := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hac hwv (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  calc
    _ ≤ (‖p - (axisMidpoint y w + a • w)‖ +
        ‖axisMidpoint x v - (axisMidpoint y w + c • w)‖) +
        ‖(a - c) • (w - b • v)‖ := (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ < 20 * r := by linarith

/-- A common doubled cover of aligned children can be replaced by an exact unit
cover on one of those children's axes. -/
theorem aligned_common_cover {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hr : r ≤ 1 / 160)
    {x v x' v' y w u : Space} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) (hw : ‖w‖ = 1)
    (hvu : ‖v - u‖ ≤ 1 / 10) (hv'u : ‖v' - u‖ ≤ 1 / 10)
    (hmid : ‖axisMidpoint x v‖ ≤ 1)
    (halign : inner ℝ v (axisMidpoint x v) = inner ℝ v' (axisMidpoint x' v'))
    (hT : Tube s x v ⊆ doubled r y w) (hT' : Tube s x' v' ⊆ doubled r y w) :
    Tube s x v ⊆ Tube (320 * r) x' v' := by
  have hr0 : 0 < r := hs.trans_le hsr
  have hline : Tube s x v ⊆ thickening (20 * r) (axisLine x' v') := by
    intro p hp
    obtain ⟨a, ha, hpa⟩ := doubled_cover_representative hs hv' hw hT' p (hT hp)
    exact mem_thickening_iff.mpr ⟨_, ⟨a, rfl⟩, by simpa only [dist_eq_norm] using hpa⟩
  simpa only [show (16 : ℝ) * (20 * r) = 320 * r by ring] using
    aligned_line_to_unit hs (by linarith : s ≤ 20 * r) (by linarith : 20 * r ≤ 1 / 8)
      hv hv' hvu hv'u hmid halign hline

end WangZahlLot.Obl.wz_multiscale_finite_tower
