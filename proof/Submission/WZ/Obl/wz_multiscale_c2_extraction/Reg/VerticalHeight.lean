-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.VerticalHeight.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ShadingHeight
import Submission.WZ.Obl.wz_grains_nonsingular_slices.NearHorizontal

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open WangZahlLot.Obl.wz_grains_nonsingular_slices
open scoped ENNReal

/-- A tube with vertical direction at least `θ` has uniformly bounded area in
every horizontal slice. The coordinate-square estimate loses `θ^2`, which is
sufficient when `θ` is an arbitrarily small power of the tube radius. -/
theorem vertical_tube_slice_area {δ θ : ℝ} {x v : Space}
    (hδ : 0 < δ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hv : ‖v‖ = 1) (hvθ : θ ≤ |v 2|)
    {Y : Set Space} (hY : Y ⊆ Tube δ x v) (z : ℝ) :
    (∫⁻ u, volume (grainFib (fun _ => 0) Y u z)) ≤ ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2) := by
  have hΔ : ∀ Δ : ℝ, 0 ≤ Δ → Δ * |v 2| ≤ 2 * δ → Δ ≤ 2 * δ / θ := by
    intro Δ hΔ hbound
    exact (le_div_iff₀ hθ).mpr ((mul_le_mul_of_nonneg_left hvθ hΔ).trans hbound)
  have hfib : ∀ u, volume (grainFib (fun _ => 0) (Tube δ x v) u z) ≤
      ENNReal.ofReal (4 * δ / θ) := by
    intro u
    apply nh_fibre_le hv (by norm_num)
    intro Δ hΔ0 _ hbound _
    have hd := hΔ Δ hΔ0 hbound
    have hδdiv : δ ≤ δ / θ := (le_div_iff₀ hθ).mpr
      ((mul_le_mul_of_nonneg_left hθ1 hδ.le).trans_eq (mul_one _))
    rw [mul_div_assoc] at hd ⊢
    linarith
  have hpos : volume (PS (fun _ => 0) (Tube δ x v) z) ≤ ENNReal.ofReal (6 * δ / θ) := by
    apply nh_volume_le_of_abs
    apply nh_PS_diam hv (by norm_num)
    intro Δ hΔ0 _ hbound
    have hd := hΔ Δ hΔ0 hbound
    have hδdiv : δ ≤ δ / θ := (le_div_iff₀ hθ).mpr
      ((mul_le_mul_of_nonneg_left hθ1 hδ.le).trans_eq (mul_one _))
    have hv0 := nh_abs_coord_v hv 0
    simp only [zero_mul, add_zero]
    have hv0' := mul_le_mul_of_nonneg_left hv0 hΔ0
    rw [mul_div_assoc] at hd ⊢
    linarith
  calc
    _ ≤ ENNReal.ofReal (4 * δ / θ) *
        volume (PS (fun _ => 0) (Tube δ x v) z ∩ PS (fun _ => 0) (Tube δ x v) z) :=
      nh_slice_le hY hY hfib
    _ ≤ ENNReal.ofReal (4 * δ / θ) * ENNReal.ofReal (6 * δ / θ) := by
      rw [inter_self]
      exact mul_le_mul' le_rfl hpos
    _ = ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

theorem vertical_tube_height_mass {δ θ : ℝ} {x v : Space}
    (hδ : 0 < δ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hv : ‖v‖ = 1) (hvθ : θ ≤ |v 2|)
    {Y : Set Space} (hYm : MeasurableSet Y) (hY : Y ⊆ Tube δ x v) (l u : ℝ) :
    volume (Y ∩ (fun p : Space => p 2) ⁻¹' Icc l u) ≤
      ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2) * ENNReal.ofReal (u - l) := by
  let S := Y ∩ (fun p : Space => p 2) ⁻¹' Icc l u
  have hc : Continuous (fun p : Space => p 2) := by fun_prop
  have hSm : MeasurableSet S := hYm.inter (hc.measurable measurableSet_Icc)
  have hST : S ⊆ Tube δ x v := inter_subset_left.trans hY
  have hslice : ∀ z, (∫⁻ w, volume (grainFib (fun _ => 0) S w z)) ≤
      (Icc l u).indicator (fun _ => ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2)) z := by
    intro z
    by_cases hz : z ∈ Icc l u
    · rw [indicator_of_mem hz]
      exact vertical_tube_slice_area hδ hθ hθ1 hv hvθ hST z
    · rw [indicator_of_notMem hz, nh_slice_eq_zero]
      rintro ⟨p, hp, rfl⟩
      exact hz hp.2
  calc
    volume S = ∫⁻ z, ∫⁻ w, volume (grainFib (fun _ => 0) S w z) :=
      volume_eq_lintegral_grainFib continuous_const hSm
    _ ≤ ∫⁻ z, (Icc l u).indicator (fun _ => ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2)) z :=
      lintegral_mono hslice
    _ = ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2) * ENNReal.ofReal (u - l) := by
      rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]

/-- Empty shadings may remain on the nearly horizontal tubes after refinement. -/
theorem vertical_shadingHeightMeasure {δ θ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hδ : 0 < δ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hv : ∀ i, ‖v i‖ = 1) (hYm : ∀ i, MeasurableSet (Y i))
    (hY : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hvertical : ∀ i, Y i = ∅ ∨ θ ≤ |v i 2|) (l u : ℝ) :
    shadingHeightMeasure Y (Icc l u) ≤
      ENNReal.ofReal (24 * n * δ ^ 2 / θ ^ 2) * ENNReal.ofReal (u - l) := by
  rw [shadingHeightMeasure_apply Y measurableSet_Icc]
  calc
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2) * ENNReal.ofReal (u - l) := by
      apply Finset.sum_le_sum
      intro i _
      rcases hvertical i with hi | hi
      · simp [restrictShadingHeights, hi]
      · exact vertical_tube_height_mass hδ hθ hθ1 (hv i) hi (hYm i) (hY i) l u
    _ = ENNReal.ofReal (24 * n * δ ^ 2 / θ ^ 2) * ENNReal.ofReal (u - l) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show 24 * (n : ℝ) * δ ^ 2 / θ ^ 2 = (n : ℝ) * (24 * δ ^ 2 / θ ^ 2) by ring,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
