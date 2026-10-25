-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_subtube_selection.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Geometry of unit tubes inside a coarse tube

Elementary facts about `thickening d (segment ℝ x (x + v))` used for the sub-tube selection:
the two possible positions of a unit tube inside the `ρ/2`-thickening of a unit segment,
containment of tubes with close parameters, and translation.
-/

namespace WangZahlLot.Obl.wz_coarse_subtube_selection

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

/-- A unit `δ`-tube inside the `ρ/2`-thickening of the unit segment `[y, y + w]` starts within
`3ρ/2` of `y` and points within `2ρ` of `w`, or starts within `3ρ/2` of `y + w` and points
within `2ρ` of `-w`. -/
theorem endpoint_alternative {δ ρ : ℝ} (hδ : 0 < δ) {x v y w : Space} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1)
    (hsub : thickening δ (segment ℝ x (x + v)) ⊆ thickening (ρ / 2) (segment ℝ y (y + w))) :
    (‖x - y‖ < 3 * ρ / 2 ∧ ‖v - w‖ < 2 * ρ) ∨
      (‖x - (y + w)‖ < 3 * ρ / 2 ∧ ‖v + w‖ < 2 * ρ) := by
  have hx : x ∈ thickening (ρ / 2) (segment ℝ y (y + w)) :=
    hsub (self_subset_thickening hδ _ (left_mem_segment ℝ _ _))
  have hxv : x + v ∈ thickening (ρ / 2) (segment ℝ y (y + w)) :=
    hsub (self_subset_thickening hδ _ (right_mem_segment ℝ _ _))
  rw [mem_thickening_iff] at hx hxv
  obtain ⟨z, hz, hxz⟩ := hx
  obtain ⟨z', hz', hxz'⟩ := hxv
  rw [segment_eq_image'] at hz hz'
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz'
  simp only [add_sub_cancel_left] at hxz hxz'
  rw [dist_eq_norm] at hxz hxz'
  have hvd : ‖v - (t - s) • w‖ < ρ := by
    have he : v - (t - s) • w = (x + v - (y + t • w)) - (x - (y + s • w)) := by
      module
    rw [he]
    calc _ ≤ ‖x + v - (y + t • w)‖ + ‖x - (y + s • w)‖ := norm_sub_le _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add hxz' hxz
      _ = ρ := by ring
  have hnorm (a : ℝ) : ‖a • w‖ = |a| := by rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
  have hts : 1 - ρ < |t - s| := by
    have h2 := norm_sub_norm_le v ((t - s) • w)
    rw [hv, hnorm] at h2
    linarith
  rcases le_total s t with hst | hst
  · left
    rw [abs_of_nonneg (sub_nonneg.mpr hst)] at hts
    constructor
    · have he : x - y = (x - (y + s • w)) + s • w := by abel
      rw [he]
      calc _ ≤ ‖x - (y + s • w)‖ + ‖s • w‖ := norm_add_le _ _
        _ = ‖x - (y + s • w)‖ + s := by rw [hnorm, abs_of_nonneg hs0]
        _ < ρ / 2 + ρ := by linarith
        _ = 3 * ρ / 2 := by ring
    · have he : v - w = (v - (t - s) • w) - (1 - (t - s)) • w := by
        module
      rw [he]
      calc _ ≤ ‖v - (t - s) • w‖ + ‖(1 - (t - s)) • w‖ := norm_sub_le _ _
        _ = ‖v - (t - s) • w‖ + (1 - (t - s)) := by
          rw [hnorm, abs_of_nonneg (by linarith)]
        _ < ρ + ρ := by linarith
        _ = 2 * ρ := by ring
  · right
    rw [abs_of_nonpos (sub_nonpos.mpr hst)] at hts
    constructor
    · have he : x - (y + w) = (x - (y + s • w)) - (1 - s) • w := by
        module
      rw [he]
      calc _ ≤ ‖x - (y + s • w)‖ + ‖(1 - s) • w‖ := norm_sub_le _ _
        _ = ‖x - (y + s • w)‖ + (1 - s) := by rw [hnorm, abs_of_nonneg (by linarith)]
        _ < ρ / 2 + ρ := by linarith
        _ = 3 * ρ / 2 := by ring
    · have he : v + w = (v - (t - s) • w) + (1 + (t - s)) • w := by
        module
      rw [he]
      calc _ ≤ ‖v - (t - s) • w‖ + ‖(1 + (t - s)) • w‖ := norm_add_le _ _
        _ = ‖v - (t - s) • w‖ + (1 + (t - s)) := by
          rw [hnorm, abs_of_nonneg (by linarith)]
        _ < ρ + ρ := by linarith
        _ = 2 * ρ := by ring

/-- A tube whose parameters are within `ε` of those of another one lies in the
`(δ + 2ε)`-thickening of the other segment. -/
theorem tube_subset_of_close {δ R ε : ℝ} {x v x' v' : Space}
    (hx : ‖x' - x‖ ≤ ε) (hv : ‖v' - v‖ ≤ ε) (hR : δ + 2 * ε ≤ R) :
    thickening δ (segment ℝ x' (x' + v')) ⊆ thickening R (segment ℝ x (x + v)) := by
  intro p hp
  rw [mem_thickening_iff] at hp ⊢
  obtain ⟨z, hz, hpz⟩ := hp
  rw [segment_eq_image'] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  simp only [add_sub_cancel_left] at hpz
  refine ⟨x + t • v, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨t, ⟨ht0, ht1⟩, by simp only [add_sub_cancel_left]⟩
  · have hε : 0 ≤ ε := (norm_nonneg _).trans hx
    have hd : dist (x' + t • v') (x + t • v) ≤ 2 * ε := by
      rw [dist_eq_norm]
      have he : x' + t • v' - (x + t • v) = (x' - x) + t • (v' - v) := by
        module
      rw [he]
      calc _ ≤ ‖x' - x‖ + ‖t • (v' - v)‖ := norm_add_le _ _
        _ = ‖x' - x‖ + t * ‖v' - v‖ := by rw [norm_smul, Real.norm_of_nonneg ht0]
        _ ≤ ε + 1 * ε := by
          have := mul_le_mul ht1 hv (norm_nonneg _) zero_le_one
          linarith
        _ = 2 * ε := by ring
    calc dist p (x + t • v) ≤ dist p (x' + t • v') + dist (x' + t • v') (x + t • v) :=
          dist_triangle _ _ _
      _ < δ + 2 * ε := by linarith
      _ ≤ R := hR

/-- Thickening a segment that lies in the `a`-thickening of another. -/
theorem thickening_subset_of_tube_subset {δ a b : ℝ} (hδ : 0 < δ) {x v y w : Space}
    (hsub : thickening δ (segment ℝ x (x + v)) ⊆ thickening a (segment ℝ y (y + w))) :
    thickening b (segment ℝ x (x + v)) ⊆ thickening (b + a) (segment ℝ y (y + w)) :=
  (thickening_subset_of_subset b ((self_subset_thickening hδ _).trans hsub)).trans
    (thickening_thickening_subset b a _)

/-- Translating a tube by `-c`. -/
theorem tube_sub_translate (δ : ℝ) (x v c : Space) :
    thickening δ (segment ℝ (x - c) (x - c + v)) =
      (fun p => c + p) ⁻¹' thickening δ (segment ℝ x (x + v)) := by
  ext p
  simp only [mem_preimage, mem_thickening_iff]
  constructor
  · rintro ⟨z, hz, hd⟩
    refine ⟨c + z, ?_, ?_⟩
    · have h := (mem_segment_translate ℝ c).mpr hz
      have e1 : c + (x - c) = x := by abel
      have e2 : c + (x - c + v) = x + v := by abel
      rwa [e1, e2] at h
    · rw [dist_add_left]; exact hd
  · rintro ⟨z, hz, hd⟩
    refine ⟨z - c, ?_, ?_⟩
    · rw [← mem_segment_translate ℝ c]
      have e1 : c + (x - c) = x := by abel
      have e2 : c + (x - c + v) = x + v := by abel
      have e3 : c + (z - c) = z := by abel
      rwa [e1, e2, e3]
    · have he : dist p (z - c) = dist (c + p) z := by
        rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
      rw [he]; exact hd

/-- A unit tube inside the `ρ/2`-thickening of `[y, y + w]` (`‖w‖ = 1`, `ρ ≤ 1`), translated
by minus the midpoint, lies in the unit ball. -/
theorem translated_tube_subset_ball {δ ρ : ℝ} (hρ1 : ρ ≤ 1) {x v y w : Space} (hw : ‖w‖ = 1)
    (hsub : thickening δ (segment ℝ x (x + v)) ⊆ thickening (ρ / 2) (segment ℝ y (y + w))) :
    thickening δ (segment ℝ (x - (y + (1 / 2 : ℝ) • w)) (x - (y + (1 / 2 : ℝ) • w) + v)) ⊆
      ball (0 : Space) 1 := by
  intro p hp
  rw [tube_sub_translate] at hp
  have hq := hsub hp
  rw [mem_thickening_iff] at hq
  obtain ⟨z, hz, hd⟩ := hq
  rw [segment_eq_image'] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  simp only [add_sub_cancel_left] at hd
  rw [mem_ball, dist_zero_right]
  have hzc : dist (y + t • w) (y + (1 / 2 : ℝ) • w) ≤ 1 / 2 := by
    rw [dist_eq_norm]
    have he : y + t • w - (y + (1 / 2 : ℝ) • w) = (t - 1 / 2) • w := by
      module
    rw [he, norm_smul, hw, mul_one, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hp' : ‖p‖ = dist (y + (1 / 2 : ℝ) • w + p) (y + (1 / 2 : ℝ) • w) := by
    rw [dist_eq_norm]; congr 1; abel
  rw [hp']
  calc _ ≤ dist (y + (1 / 2 : ℝ) • w + p) (y + t • w) +
        dist (y + t • w) (y + (1 / 2 : ℝ) • w) := dist_triangle _ _ _
    _ < ρ / 2 + 1 / 2 := add_lt_add_of_lt_of_le hd hzc
    _ ≤ 1 := by linarith

end WangZahlLot.Obl.wz_coarse_subtube_selection
