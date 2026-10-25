-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.AlignedAxes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.AxisGeometry
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (doubled centered_segment)

noncomputable def axisMidpoint (x v : Space) : Space := x + (1 / 2 : ℝ) • v

lemma unit_near_multiple {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (a : ℝ) :
    min ‖v - w‖ ‖v + w‖ ≤ 2 * ‖v - a • w‖ := by
  have he := abs_norm_sub_norm_le v (a • w)
  rw [hv, norm_smul, Real.norm_eq_abs, hw, mul_one] at he
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha] at he
    apply (min_le_left _ _).trans
    have htri := norm_add_le (v - a • w) ((a - 1) • w)
    have hh : v - a • w + (a - 1) • w = v - w := by module
    rw [hh, norm_smul, Real.norm_eq_abs, hw, mul_one] at htri
    rw [abs_sub_comm 1 a] at he
    linarith
  · rw [abs_of_neg (lt_of_not_ge ha)] at he
    apply (min_le_right _ _).trans
    have htri := norm_add_le (v - a • w) ((a + 1) • w)
    have hh : v - a • w + (a + 1) • w = v + w := by module
    rw [hh, norm_smul, Real.norm_eq_abs, hw, mul_one] at htri
    have hh' : 1 - -a = a + 1 := by ring
    rw [hh'] at he
    linarith

lemma mem_doubled_axis_param {r : ℝ} {y w p : Space} (hp : p ∈ doubled r y w) :
    ∃ a : ℝ, |a| ≤ 1 ∧ ‖p - (axisMidpoint y w + a • w)‖ < 2 * r := by
  obtain ⟨t, ht, hp⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  refine ⟨2 * t - 1, abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  convert hp using 1
  congr 1
  dsimp [axisMidpoint]
  module

/-- A unit child in a doubled parent has a close projective direction. -/
lemma doubled_axis_angle {s r : ℝ} (hs : 0 < s) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : Tube s x v ⊆ doubled r y w) :
    min ‖v - w‖ ‖v + w‖ ≤ 8 * r := by
  obtain ⟨a, ha, hxa⟩ := mem_doubled_axis_param
    (hT (self_subset_thickening hs _ (left_mem_segment ℝ _ _)))
  obtain ⟨b, hb, hxb⟩ := mem_doubled_axis_param
    (hT (self_subset_thickening hs _ (right_mem_segment ℝ _ _)))
  have he : v - (b - a) • w =
      (x + v - (axisMidpoint y w + b • w)) - (x - (axisMidpoint y w + a • w)) := by module
  have hclose : ‖v - (b - a) • w‖ < 4 * r := by
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  exact (unit_near_multiple hv hw (b - a)).trans (by linarith)

/-- The scalar midpoint alignment turns transverse closeness into full midpoint
closeness. It remains stable as the direction changes. -/
lemma aligned_midpoint_distance {m n v w : Space} (hw : ‖w‖ = 1)
    (halign : inner ℝ v m = inner ℝ w n) (a : ℝ) :
    ‖m - n‖ ≤ 2 * ‖m - n - a • w‖ + ‖v - w‖ * ‖m‖ := by
  have hww : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have he : inner ℝ w (m - n) = inner ℝ (w - v) m := by
    rw [inner_sub_right, inner_sub_left]
    linarith
  have hfirst : |inner ℝ w (m - n)| ≤ ‖v - w‖ * ‖m‖ := by
    rw [he]
    simpa only [norm_sub_rev] using abs_real_inner_le_norm (w - v) m
  have hsecond : |inner ℝ w (m - n - a • w)| ≤ ‖m - n - a • w‖ := by
    simpa only [hw, one_mul] using abs_real_inner_le_norm w (m - n - a • w)
  have ha : |a| ≤ ‖v - w‖ * ‖m‖ + ‖m - n - a • w‖ := by
    have hi : a = inner ℝ w (m - n) - inner ℝ w (m - n - a • w) := by
      simp only [inner_sub_right, inner_smul_right, hww]
      ring
    calc
      |a| = |inner ℝ w (m - n) - inner ℝ w (m - n - a • w)| := congrArg abs hi
      _ ≤ _ := (abs_sub _ _).trans (add_le_add hfirst hsecond)
  have htri := norm_add_le (m - n - a • w) (a • w)
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, hw, mul_one] at htri
  linarith

lemma norm_add_lower_of_common_direction {v w u : Space}
    (hv : ‖v‖ = 1) (hvu : ‖v - u‖ ≤ 1 / 10) (hwu : ‖w - u‖ ≤ 1 / 10) :
    (1 : ℝ) ≤ ‖v + w‖ := by
  have hd : ‖v - w‖ ≤ 1 / 5 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub v u w
    rw [norm_sub_rev u w] at hh
    linarith
  have he : v + w + (v - w) = (2 : ℝ) • v := by module
  have hh := norm_add_le (v + w) (v - w)
  rw [he, norm_smul, Real.norm_eq_abs, hv] at hh
  norm_num at hh
  linarith

/-- For axes in one direction cap with a common axial midpoint scalar, doubled
containment can be replaced by unit-segment containment with a fixed radius loss. -/
theorem aligned_doubled_to_unit {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hr : r ≤ 1 / 16)
    {x v y w u : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvu : ‖v - u‖ ≤ 1 / 10) (hwu : ‖w - u‖ ≤ 1 / 10)
    (hmid : ‖axisMidpoint x v‖ ≤ 1)
    (halign : inner ℝ v (axisMidpoint x v) = inner ℝ w (axisMidpoint y w))
    (hT : Tube s x v ⊆ doubled r y w) : Tube s x v ⊆ Tube (32 * r) y w := by
  have hr0 : 0 < r := hs.trans_le hsr
  have hangle := doubled_axis_angle hs hv hw hT
  have hvw : ‖v - w‖ ≤ 8 * r := by
    rcases min_le_iff.mp hangle with hh | hh
    · exact hh
    · have hh' := norm_add_lower_of_common_direction hv hvu hwu
      linarith
  have hmidmem : axisMidpoint x v ∈ Tube s x v := self_subset_thickening hs _
    (by simpa only [axisMidpoint, zero_smul, add_zero] using
      centered_segment x v (a := 0) (by norm_num))
  obtain ⟨a, ha, hnear⟩ := mem_doubled_axis_param (hT hmidmem)
  have hnear' : ‖axisMidpoint x v - axisMidpoint y w - a • w‖ < 2 * r := by
    simpa only [sub_add_eq_sub_sub] using hnear
  have hcenters : ‖axisMidpoint x v - axisMidpoint y w‖ < 12 * r := by
    have hh := aligned_midpoint_distance hw halign a
    have hh' := mul_le_mul hvw hmid (norm_nonneg _) (by positivity : 0 ≤ 8 * r)
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
  have hlast : ‖(t - 1 / 2) • (v - w)‖ ≤ 4 * r := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul habs hvw (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  calc
    _ ≤ (‖p - (x + t • v)‖ + ‖axisMidpoint x v - axisMidpoint y w‖) +
        ‖(t - 1 / 2) • (v - w)‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < 32 * r := by linarith

end WangZahlLot.Obl.wz_multiscale_finite_tower
