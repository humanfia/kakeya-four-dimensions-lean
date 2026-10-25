-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_depth_step.Shifts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_depth_step.Alignment
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_depth_step

open MeasureTheory Set Metric

/-- A bounded move along a unit segment keeps its endpoints near the same axis.
The second line may be moved by any amount along its own axis. -/
lemma shifted_endpoints_near_axis {R a b : ℝ} (hR : 0 < R) (ha : |a| ≤ 1)
    {x v y w : Space}
    (h₀ : ∃ t : ℝ, ‖x - (y + t • w)‖ < R)
    (h₁ : ∃ t : ℝ, ‖x + v - (y + t • w)‖ < R) :
    ∀ p ∈ ({x + a • v, x + a • v + v} : Set Space),
      ∃ t : ℝ, ‖p - ((y + b • w) + t • w)‖ < 5 * R := by
  obtain ⟨t₀, ht₀⟩ := h₀
  obtain ⟨t₁, ht₁⟩ := h₁
  let e₀ := x - (y + t₀ • w)
  let e₁ := x + v - (y + t₁ • w)
  have hparam (τ : ℝ) (hτ : -1 ≤ τ ∧ τ ≤ 2) :
      ∃ t : ℝ, ‖x + τ • v - ((y + b • w) + t • w)‖ < 5 * R := by
    refine ⟨(1 - τ) * t₀ + τ * t₁ - b, ?_⟩
    have he : x + τ • v - ((y + b • w) + ((1 - τ) * t₀ + τ * t₁ - b) • w) =
        (1 - τ) • e₀ + τ • e₁ := by dsimp [e₀, e₁]; module
    have hτabs : |τ| ≤ 2 := abs_le.mpr ⟨by linarith [hτ.1], hτ.2⟩
    have hτabs' : |1 - τ| ≤ 2 := abs_le.mpr ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    rw [he]
    calc
      _ ≤ ‖(1 - τ) • e₀‖ + ‖τ • e₁‖ := norm_add_le _ _
      _ = |1 - τ| * ‖e₀‖ + |τ| * ‖e₁‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 2 * R + 2 * R := by
        exact add_le_add
          (mul_le_mul hτabs' ht₀.le (norm_nonneg _) (by norm_num))
          (mul_le_mul hτabs ht₁.le (norm_nonneg _) (by norm_num))
      _ < 5 * R := by linarith
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · exact hparam a ⟨(abs_le.mp ha).1, by linarith [(abs_le.mp ha).2]⟩
  · have hp' : p = x + (a + 1) • v := by
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      module
    rw [hp']
    exact hparam (a + 1) ⟨by linarith [(abs_le.mp ha).1], by linarith [(abs_le.mp ha).2]⟩

/-- The common-plane enlargement remains uniform after bounded axial moves. -/
theorem shifted_aligned_cover {R s a b : ℝ} (hR : 0 < R) (ha : |a| ≤ 1)
    {u x v y w : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huw : 1 / 4 ≤ |inner ℝ u w|)
    (hplane : inner ℝ u (x + a • v + (1 / 2 : ℝ) • v -
      (y + b • w + (1 / 2 : ℝ) • w)) = 0)
    (h₀ : ∃ t : ℝ, ‖x - ((y + (1 / 2 : ℝ) • w) + t • w)‖ < R)
    (h₁ : ∃ t : ℝ, ‖x + v - ((y + (1 / 2 : ℝ) • w) + t • w)‖ < R) :
    Tube s (x + a • v) v ⊆ Tube (s + 40 * R) (y + b • w) w := by
  have hn := shifted_endpoints_near_axis (b := b) hR ha h₀ h₁
  have hn' : ∀ p ∈ ({x + a • v, x + a • v + v} : Set Space),
      ∃ t : ℝ, ‖p - ((y + b • w + (1 / 2 : ℝ) • w) + t • w)‖ < 5 * R := by
    intro p hp
    obtain ⟨t, ht⟩ := hn p hp
    refine ⟨t, ?_⟩
    convert ht using 1; congr 1; module
  obtain ⟨hleft, hright⟩ := aligned_endpoints_near_unit_segment (by positivity) hu hv hw huw hplane hn'
  have hseg : segment ℝ (x + a • v) (x + a • v + v) ⊆ Tube (8 * (5 * R)) (y + b • w) w :=
    ((convex_segment _ _).thickening _).segment_subset hleft hright
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
  obtain ⟨z', hz', hzz'⟩ := mem_thickening_iff.mp (hseg hz)
  apply mem_thickening_iff.mpr
  refine ⟨z', hz', ?_⟩
  have ht := (dist_triangle p z z').trans_lt (add_lt_add hpz hzz')
  convert ht using 1; ring

/-- The parts lost by shifting along the axis lie near the two segment endpoints. -/
lemma shift_loss_subset {δ H a : ℝ} {x v : Space} (ha : |a| ≤ H) :
    Tube δ x v \ Tube δ (x + a • v) v ⊆
      thickening δ ((fun t : ℝ => x + t • v) '' (Icc 0 1 ∩ Iic H)) ∪
      thickening δ ((fun t : ℝ => x + t • v) '' (Icc 0 1 ∩ Ici (1 - H))) := by
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp.1
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [add_sub_cancel_left] at hpz
  have hout : t < a ∨ a + 1 < t := by
    by_contra h
    push Not at h
    have hnew : x + t • v ∈ segment ℝ (x + a • v) (x + a • v + v) := by
      rw [segment_eq_image']
      refine ⟨t - a, ⟨by linarith [h.1], by linarith [h.2]⟩, ?_⟩
      module
    exact hp.2 (mem_thickening_iff.mpr ⟨x + t • v, hnew, hpz⟩)
  rcases hout with hlo | hhi
  · left
    exact mem_thickening_iff.mpr ⟨x + t • v,
      ⟨t, ⟨ht, by exact le_of_lt (hlo.trans_le (abs_le.mp ha).2)⟩, rfl⟩, hpz⟩
  · right
    exact mem_thickening_iff.mpr ⟨x + t • v,
      ⟨t, ⟨ht, by change 1 - H ≤ t; linarith [(abs_le.mp ha).1]⟩, rfl⟩, hpz⟩

/-- Quantitative endpoint loss for an axial shift, independent of the shading. -/
theorem shift_loss_volume {δ H a : ℝ} (hδ : 0 < δ) (hH : 0 ≤ H)
    {x v : Space} (hv : ‖v‖ = 1) (ha : |a| ≤ H) :
    volume (Tube δ x v \ Tube δ (x + a • v) v) ≤
      ENNReal.ofReal (256 * (2 * H + δ) * δ ^ 2) := by
  let T₀ : Set ℝ := Icc 0 1 ∩ Iic H
  let T₁ : Set ℝ := Icc 0 1 ∩ Ici (1 - H)
  have h₀ := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    x v hv (show T₀ ⊆ Icc 0 1 from inter_subset_left) hδ hH (by
      intro s hs t ht
      simp only [T₀, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic] at hs ht
      rw [Real.dist_eq, abs_le]
      exact ⟨by linarith [hs.1.1, ht.2], by linarith [ht.1.1, hs.2]⟩)
  have h₁ := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    x v hv (show T₁ ⊆ Icc 0 1 from inter_subset_left) hδ hH (by
      intro s hs t ht
      simp only [T₁, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici] at hs ht
      rw [Real.dist_eq, abs_le]
      exact ⟨by linarith [hs.2, ht.1.2], by linarith [ht.2, hs.1.2]⟩)
  calc
    _ ≤ volume (thickening δ ((fun t : ℝ => x + t • v) '' T₀) ∪
        thickening δ ((fun t : ℝ => x + t • v) '' T₁)) := measure_mono (shift_loss_subset ha)
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (128 * (2 * H + δ) * δ ^ 2) +
        ENNReal.ofReal (128 * (2 * H + δ) * δ ^ 2) := add_le_add h₀ h₁
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end WangZahlLot.Obl.wz_tower_depth_step
