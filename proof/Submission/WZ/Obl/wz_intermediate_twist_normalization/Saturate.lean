-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.Saturate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.NormTube

/-!
# Saturated shadings of normalized tubes

The zoomed shading of a class tube is a thin plate inside its normalized tube. Its
*saturation* is the part of the normalized tube lying over the projected points where the
zoomed shading has a fibre of positive length. The fibres of the projection `P_(f - f 0)`
cross the normalized tube along a length at least `ρ / 3` over such points, while the zoomed
shading has fibres of length at most `Z ℓ`, `ℓ = 6 δ / (|f 0| - 2)`. Hence the saturation has
mass at least `ρ Z (|f 0| - 2) / (18 δ)` times the mass of the shading, and it projects into
the zoomed projection of the shading.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN proj lineAt fib
  measurable_fib volume_eq_lintegral_fib volume_grainFib_tube_le abs_lt_one_of_grainFib)
open WangZahlLot.Obl.wz_grains_nonsingular_slices (ofTwist grainFib ofTwist_zero ofTwist_one
  ofTwist_two grainFib_mono)
open WangZahlLot.Obl.wz_compact_offset_normalization (norm_sq_eq abs_coord_le_norm mem_tube_iff)

/-- The planar projection map. -/
def pmap (f : ℝ → ℝ) (p : Space) : ℝ × ℝ := (p 0 + f (p 2) * p 1, p 2)

theorem proj_eq_image (f : ℝ → ℝ) (E : Set Space) : proj f E = pmap f '' E := rfl

theorem pmap_ofTwist (f : ℝ → ℝ) (u y z : ℝ) : pmap f (ofTwist f u y z) = (u, z) := by
  simp only [pmap, ofTwist_zero, ofTwist_one, ofTwist_two]
  ext <;> simp

theorem continuous_pmap {f : ℝ → ℝ} (hf : Continuous f) : Continuous (pmap f) := by
  unfold pmap
  have h0 : Continuous fun p : Space => p 0 := by fun_prop
  have h1 : Continuous fun p : Space => p 1 := by fun_prop
  have h2 : Continuous fun p : Space => p 2 := by fun_prop
  exact (h0.add ((hf.comp h2).mul h1)).prodMk h2

theorem unzoom_pmap {f : ℝ → ℝ} {Z : ℝ} (hZ : Z ≠ 0) (α β : ℝ) (p : Space) :
    unzoom f Z α β (pmap (fun w => f w - f 0) (zoom Z (f 0) α β p)) = pmap f p :=
  unzoom_proj hZ α β p

/-- Fibre lengths of subsets of a transverse tube inside the unit ball. -/
theorem volume_grainFib_le_of_subset {δ : ℝ} {x v : Space} {f : ℝ → ℝ} (hf : SlopeN f)
    (hc : 100 < |f 0|) (hv : ‖v‖ = 1) (hv2 : (1 / 2 : ℝ) ≤ |v 2|)
    (hT : tube δ x v ⊆ ball 0 1) {A : Set Space} (hA : A ⊆ tube δ x v) (u z : ℝ) :
    volume (grainFib f A u z) ≤ ENNReal.ofReal (6 * δ / (|f 0| - 2)) := by
  by_cases hne : (grainFib f (tube δ x v) u z).Nonempty
  · have hz := abs_lt_one_of_grainFib hT hne
    have hfz : |f z - f 0| ≤ 2 := hf.sub_le hz.le
    have hm : |f 0| - 2 ≤ |f z| := by
      have := abs_sub_abs_le_abs_sub (f 0) (f z)
      rw [abs_sub_comm] at this
      linarith
    exact (measure_mono (grainFib_mono hA u z)).trans
      (volume_grainFib_tube_le hv hv2 (by linarith) hm)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : grainFib f A u z = ∅ := subset_empty_iff.mp (hne ▸ grainFib_mono hA u z)
    rw [h0, measure_empty]
    exact zero_le

/-- The height window of the normalized tube. -/
def nwin (Z c β ρ e δ : ℝ) (x v : Space) : Set Space :=
  {p | nhb Z c β ρ e x v + δ ≤ p 2 ∧ p 2 ≤ nhb Z c β ρ e x v + nuz Z c β v - δ}

theorem measurableSet_nwin (Z c β ρ e δ : ℝ) (x v : Space) :
    MeasurableSet (nwin Z c β ρ e δ x v) := by
  have h2 : Continuous fun p : Space => p 2 := by fun_prop
  exact (measurableSet_le measurable_const h2.measurable).inter
    (measurableSet_le h2.measurable measurable_const)

/-- The positivity set of the zoomed fibres. -/
def nposD (f : ℝ → ℝ) (Z α β : ℝ) (A : Set Space) : Set (ℝ × ℝ) :=
  {q | 0 < fib (fun w => f w - f 0) (zoom Z (f 0) α β '' A) q}

/-- The saturated shading. -/
def nsat (f : ℝ → ℝ) (Z α β ρ e : ℝ) (x v : Space) (A : Set Space) : Set Space :=
  ntube Z (f 0) α β ρ e x v ∩ pmap (fun w => f w - f 0) ⁻¹' nposD f Z α β A

theorem nsat_subset (f : ℝ → ℝ) (Z α β ρ e : ℝ) (x v : Space) (A : Set Space) :
    nsat f Z α β ρ e x v A ⊆ ntube Z (f 0) α β ρ e x v := inter_subset_left

theorem measurableSet_nposD {f : ℝ → ℝ} (hf : Continuous f) {Z : ℝ} (hZ : Z ≠ 0) (α β : ℝ)
    {A : Set Space} (hA : MeasurableSet A) : MeasurableSet (nposD f Z α β A) := by
  have hφ : Continuous fun w => f w - f 0 := hf.sub continuous_const
  exact measurableSet_lt measurable_const
    (measurable_fib hφ (zoom_measurableSet_image hZ _ α β hA))

theorem measurableSet_nsat {f : ℝ → ℝ} (hf : Continuous f) {Z : ℝ} (hZ : Z ≠ 0)
    (α β ρ e : ℝ) (x v : Space) {A : Set Space} (hA : MeasurableSet A) :
    MeasurableSet (nsat f Z α β ρ e x v A) := by
  have hφ : Continuous fun w => f w - f 0 := hf.sub continuous_const
  exact isOpen_thickening.measurableSet.inter
    ((measurableSet_nposD hf hZ α β hA).preimage (continuous_pmap hφ).measurable)

/-- A positive fibre comes from a point of the zoomed shading. -/
theorem exists_of_mem_nposD {f : ℝ → ℝ} {Z α β : ℝ} {A : Set Space} {q : ℝ × ℝ}
    (hq : q ∈ nposD f Z α β A) :
    ∃ y0 : ℝ, ∃ p ∈ A, zoom Z (f 0) α β p = ofTwist (fun w => f w - f 0) q.1 y0 q.2 := by
  have hne : (grainFib (fun w => f w - f 0) (zoom Z (f 0) α β '' A) q.1 q.2).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : fib (fun w => f w - f 0) (zoom Z (f 0) α β '' A) q = 0 := by
      simp [fib, h]
    exact absurd hq (by simp [nposD, this])
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨p, hp, hpe⟩ := hy0
  exact ⟨y0, p, hp, hpe⟩

/-- The saturation projects into the zoomed projection of the shading. -/
theorem nsat_proj {f : ℝ → ℝ} {Z : ℝ} (hZ : Z ≠ 0) {α β ρ e : ℝ} {x v : Space}
    {A : Set Space} {p' : Space} (hp' : p' ∈ nsat f Z α β ρ e x v A) :
    ∃ p ∈ A, pmap f p = unzoom f Z α β (pmap (fun w => f w - f 0) p') := by
  obtain ⟨y0, p, hp, hpe⟩ := exists_of_mem_nposD hp'.2
  refine ⟨p, hp, ?_⟩
  rw [← unzoom_pmap hZ α β p, hpe, pmap_ofTwist]

section

variable {c δ Z ρ e r0 α β : ℝ} {x v : Space}

/-- Over a point where the zoomed shading has a fibre, the normalized tube has a fibre of
length at least `ρ / 3`. -/
theorem CG.fib_ntube_ge {f : ℝ → ℝ} (h : CG (f 0) δ Z ρ e r0 α β x v) (hf : SlopeN f)
    {A : Set Space} (hA : A ⊆ tube δ x v ∩ nwin Z (f 0) β ρ e δ x v) {q : ℝ × ℝ}
    (hq : q ∈ nposD f Z α β A) :
    ENNReal.ofReal (ρ / 3) ≤
      volume (grainFib (fun w => f w - f 0) (nsat f Z α β ρ e x v A) q.1 q.2) := by
  obtain ⟨y0, p, hp, hpe⟩ := exists_of_mem_nposD hq
  have hpT := (hA hp).1
  obtain ⟨hw1, hw2⟩ := (hA hp).2
  obtain ⟨s, hs, hds⟩ := h.zoom_near_axis hpT hw1 hw2
  have hz : |q.2| < 1 := by
    have h2 : (zoom Z (f 0) α β p) 2 = q.2 := by rw [hpe, ofTwist_two]
    rw [zoom_apply_two] at h2
    have := mem_ball_zero_iff.mp (h.hT hpT)
    have h3 := (abs_coord_le_norm p 2).trans_lt this
    rwa [h2] at h3
  have hφ : |f q.2 - f 0| ≤ 2 := hf.sub_le hz.le
  have hρ0 : 0 < ρ := by rw [h.hρ]; have := h.hZ; have := h.hδ; have := h.hc; positivity
  have hsub : Ioo (y0 - ρ / 6) (y0 + ρ / 6) ⊆
      grainFib (fun w => f w - f 0) (nsat f Z α β ρ e x v A) q.1 q.2 := by
    intro y hy
    have hy' : |y - y0| < ρ / 6 := abs_sub_lt_iff.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
    refine ⟨?_, ?_⟩
    · -- the point lies in the normalized tube
      rw [ntube, tube, mem_thickening_iff]
      refine ⟨s, hs, ?_⟩
      have hd1 : dist (ofTwist (fun w => f w - f 0) q.1 y q.2)
          (ofTwist (fun w => f w - f 0) q.1 y0 q.2) < ρ / 2 := by
        rw [dist_eq_norm]
        set w := ofTwist (fun w => f w - f 0) q.1 y q.2 -
          ofTwist (fun w => f w - f 0) q.1 y0 q.2 with hwdef
        have w0 : w 0 = -((f q.2 - f 0) * (y - y0)) := by
          rw [hwdef, PiLp.sub_apply, ofTwist_zero, ofTwist_zero]; ring
        have w1 : w 1 = y - y0 := by rw [hwdef, PiLp.sub_apply, ofTwist_one, ofTwist_one]
        have w2 : w 2 = 0 := by rw [hwdef, PiLp.sub_apply, ofTwist_two, ofTwist_two]; ring
        have hsq : ‖w‖ ^ 2 < (ρ / 2) ^ 2 := by
          rw [norm_sq_eq, w0, w1, w2]
          have h1 : (f q.2 - f 0) ^ 2 ≤ 4 := by
            have := sq_le_sq_of_abs_le hφ; linarith
          have h2 : (y - y0) ^ 2 < (ρ / 6) ^ 2 := by
            have := abs_nonneg (y - y0)
            rw [← sq_abs]
            exact pow_lt_pow_left₀ hy' this two_ne_zero
          have h3 : 0 ≤ (y - y0) ^ 2 := sq_nonneg _
          nlinarith
        exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
      calc dist (ofTwist (fun w => f w - f 0) q.1 y q.2) s
          ≤ dist (ofTwist (fun w => f w - f 0) q.1 y q.2)
              (ofTwist (fun w => f w - f 0) q.1 y0 q.2) +
            dist (ofTwist (fun w => f w - f 0) q.1 y0 q.2) s := dist_triangle _ _ _
        _ < ρ / 2 + ρ / 2 := add_lt_add hd1 (by rw [← hpe]; exact hds)
        _ = ρ := by ring
    · -- the point lies over the positivity set
      show pmap (fun w => f w - f 0) (ofTwist (fun w => f w - f 0) q.1 y q.2) ∈ nposD f Z α β A
      rw [pmap_ofTwist]
      exact hq
  calc ENNReal.ofReal (ρ / 3) = volume (Ioo (y0 - ρ / 6) (y0 + ρ / 6)) := by
        rw [Real.volume_Ioo]; congr 1; ring
    _ ≤ _ := measure_mono hsub

/-- **The saturation gains the aspect ratio.** -/
theorem CG.volume_nsat_ge {f : ℝ → ℝ} (h : CG (f 0) δ Z ρ e r0 α β x v) (hf : SlopeN f)
    {A : Set Space} (hAm : MeasurableSet A) (hA : A ⊆ tube δ x v ∩ nwin Z (f 0) β ρ e δ x v) :
    ENNReal.ofReal (ρ * Z * (|f 0| - 2) / (18 * δ)) * volume A ≤
      volume (nsat f Z α β ρ e x v A) := by
  have hfc : Continuous f := hf.continuous
  have hφ : Continuous fun w => f w - f 0 := hfc.sub continuous_const
  have hZ := h.hZ
  have hδ := h.hδ
  have hc := h.hc
  have hc2 : 0 < |f 0| - 2 := by linarith
  have hρ0 : 0 < ρ := by rw [h.hρ]; positivity
  set ℓ := 6 * δ / (|f 0| - 2) with hℓ
  have hℓ0 : 0 < ℓ := by positivity
  set B := zoom Z (f 0) α β '' A with hBdef
  have hBm : MeasurableSet B := zoom_measurableSet_image hZ.ne' _ α β hAm
  set D := nposD f Z α β A with hDdef
  have hDm : MeasurableSet D := measurableSet_nposD hfc hZ.ne' α β hAm
  set S := nsat f Z α β ρ e x v A with hSdef
  have hSm : MeasurableSet S := measurableSet_nsat hfc hZ.ne' α β ρ e x v hAm
  -- the zoomed shading has short fibres, supported on `D`
  have h2 : volume B ≤ ENNReal.ofReal (Z * ℓ) * volume D := by
    rw [volume_eq_lintegral_fib hφ hBm]
    calc ∫⁻ q, fib (fun w => f w - f 0) B q
        ≤ ∫⁻ q, D.indicator (fun _ => ENNReal.ofReal (Z * ℓ)) q := by
          refine lintegral_mono fun q => ?_
          by_cases hq : q ∈ D
          · rw [indicator_of_mem hq]
            simp only [fib]
            rw [hBdef, volume_grainFib_zoom_image f hZ α β A q.1 q.2,
              ENNReal.ofReal_mul hZ.le]
            gcongr
            exact volume_grainFib_le_of_subset hf hc h.hv h.hv2 h.hT
              (fun p hp => (hA hp).1) _ _
          · rw [indicator_of_notMem hq]
            have : ¬ 0 < fib (fun w => f w - f 0) B q := hq
            rw [not_lt, nonpos_iff_eq_zero] at this
            rw [this]
      _ = ENNReal.ofReal (Z * ℓ) * volume D := lintegral_indicator_const hDm _
  -- the saturation has long fibres over `D`
  have h3 : ENNReal.ofReal (ρ / 3) * volume D ≤ volume S := by
    rw [volume_eq_lintegral_fib hφ hSm, ← lintegral_indicator_const hDm]
    refine lintegral_mono fun q => ?_
    by_cases hq : q ∈ D
    · rw [indicator_of_mem hq]
      exact h.fib_ntube_ge hf hA hq
    · rw [indicator_of_notMem hq]
      exact zero_le
  have h1 : volume B = ENNReal.ofReal (Z ^ 2) * volume A := zoom_volume_image hZ _ α β A
  have hk : 0 ≤ ρ / (3 * Z * ℓ) := by positivity
  calc ENNReal.ofReal (ρ * Z * (|f 0| - 2) / (18 * δ)) * volume A
      = ENNReal.ofReal (ρ / (3 * Z * ℓ)) * (ENNReal.ofReal (Z ^ 2) * volume A) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hk]
        congr 2
        rw [hℓ]
        field_simp
        ring
    _ ≤ ENNReal.ofReal (ρ / (3 * Z * ℓ)) * (ENNReal.ofReal (Z * ℓ) * volume D) := by
        rw [← h1]
        gcongr
    _ = ENNReal.ofReal (ρ / 3) * volume D := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hk]
        congr 2
        field_simp
    _ ≤ volume S := h3

end

end WangZahlLot.Obl.wz_intermediate_twist_normalization
