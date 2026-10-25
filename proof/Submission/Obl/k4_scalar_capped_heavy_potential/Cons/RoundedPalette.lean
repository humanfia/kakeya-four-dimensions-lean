import Submission.Lib.K4ScalarActualSwitching.GridPalette

/-!
# Rounded velocities and their palette

Velocities are rounded to the centers of floor bins of width `δ`. Relative
palette caps on the individual bins give the rectangular caps of the rounded
velocity for every measurable set, and coarse bin caps give thin-pencil caps.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory

/-- The floor-bin index of a velocity at width `δ`. -/
noncomputable def vbin (δ v : ℝ) : ℤ := ⌊v / δ⌋

/-- The center of the floor bin `c` at width `δ`. -/
noncomputable def vcenter (δ : ℝ) (c : ℤ) : ℝ := ((c : ℝ) + 1 / 2) * δ

/-- A velocity rounded to the center of its floor bin. -/
noncomputable def vround (δ v : ℝ) : ℝ := vcenter δ (vbin δ v)

theorem measurable_vbin (δ : ℝ) : Measurable (vbin δ) :=
  Int.measurable_floor.comp (measurable_id.div_const δ)

theorem measurable_vcenter (δ : ℝ) : Measurable (vcenter δ) := measurable_from_top

theorem measurable_vround (δ : ℝ) : Measurable (vround δ) :=
  (measurable_vcenter δ).comp (measurable_vbin δ)

theorem abs_vround_sub_le {δ : ℝ} (hδ : 0 < δ) (v : ℝ) : |vround δ v - v| ≤ δ / 2 := by
  unfold vround vcenter vbin
  have h1 : (⌊v / δ⌋ : ℝ) ≤ v / δ := Int.floor_le _
  have h2 : v / δ < (⌊v / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h1' : (⌊v / δ⌋ : ℝ) * δ ≤ v := by rwa [le_div_iff₀ hδ] at h1
  have h2' : v < ((⌊v / δ⌋ : ℝ) + 1) * δ := by rwa [div_lt_iff₀ hδ] at h2
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_vround_le {δ : ℝ} (hδ : 0 < δ) (v : ℝ) : |vround δ v| ≤ |v| + δ := by
  have h := abs_vround_sub_le hδ v
  have h2 := abs_sub_abs_le_abs_sub (vround δ v) v
  linarith

/-- Relative caps on the individual floor bins give the rectangular caps of the
rounded velocity against the rounded palette, for every measurable set. -/
theorem rounded_palette_rect {Ω Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (V : Ω → ℝ) (hV : Measurable V) (π : Measure ℝ) (K : ENNReal) (δ : ℝ)
    (hatom : ∀ q (c : ℤ), μ {ω | state ω = q ∧ V ω ∈ {v : ℝ | (⌊v / δ⌋ : ℤ) = c}} ≤
      K * μ (state ⁻¹' {q}) * π {v : ℝ | (⌊v / δ⌋ : ℤ) = c}) :
    ∀ q (A : Set ℝ), MeasurableSet A →
      μ {ω | state ω = q ∧ vround δ (V ω) ∈ A} ≤ K * μ (state ⁻¹' {q}) * (π.map (vround δ)) A := by
  intro q A hA
  have hcode : Measurable (fun ω => vbin δ (V ω)) := (measurable_vbin δ).comp hV
  have h := Submission.Lib.K4ScalarActualSwitching.rectangular_rounded_palette_caps_of_atoms
    μ state hstate (fun ω => vbin δ (V ω)) hcode (vcenter δ) (measurable_vcenter δ)
    (π.map (vbin δ)) K (fun q c => by
      rw [Measure.map_apply (measurable_vbin δ) (measurableSet_singleton c)]
      exact hatom q c) q A hA
  rw [Measure.map_map (measurable_vcenter δ) (measurable_vbin δ)] at h
  exact h

/-- Coarse floor-bin caps at width `δb` give the rounded palette thin-pencil
caps at every radius `r` with `r + δ/2 ≤ δb`. -/
theorem rounded_palette_thin (π : Measure ℝ) {δ δb r : ℝ} (hδ : 0 < δ) (hδb : 0 < δb)
    (hr : r + δ / 2 ≤ δb) (pcap : ENNReal)
    (hcap : ∀ c : ℤ, π {v : ℝ | (⌊v / δb⌋ : ℤ) = c} ≤ pcap) :
    ∀ w : ℝ, (π.map (vround δ)) {v | |v - w| < r} ≤ 3 * pcap := by
  intro w
  have hmeas : MeasurableSet {v : ℝ | |v - w| < r} :=
    measurableSet_lt (measurable_id.sub measurable_const).abs measurable_const
  rw [Measure.map_apply (measurable_vround δ) hmeas]
  set c₀ : ℤ := ⌊w / δb⌋ with hc₀
  have hsub : vround δ ⁻¹' {v | |v - w| < r} ⊆
      {v : ℝ | (⌊v / δb⌋ : ℤ) = c₀ - 1} ∪ {v : ℝ | (⌊v / δb⌋ : ℤ) = c₀} ∪
        {v : ℝ | (⌊v / δb⌋ : ℤ) = c₀ + 1} := by
    intro v hv
    simp only [mem_preimage, mem_setOf_eq] at hv
    have hround := abs_vround_sub_le hδ v
    have hvw : |v - w| < δb := by
      have := abs_sub_le v (vround δ v) w
      rw [abs_sub_comm v (vround δ v)] at this
      linarith
    rw [abs_lt] at hvw
    have hw1 : (c₀ : ℝ) ≤ w / δb := Int.floor_le _
    have hw2 : w / δb < (c₀ : ℝ) + 1 := Int.lt_floor_add_one _
    have hv1 : w / δb - 1 < v / δb := by
      rw [div_sub_one hδb.ne', div_lt_div_iff_of_pos_right hδb]
      linarith
    have hv2 : v / δb < w / δb + 1 := by
      rw [div_add_one hδb.ne', div_lt_div_iff_of_pos_right hδb]
      linarith
    have hlo : c₀ - 1 ≤ ⌊v / δb⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith
    have hhi : ⌊v / δb⌋ ≤ c₀ + 1 := by
      rw [← Int.lt_add_one_iff, Int.floor_lt]
      push_cast
      linarith
    simp only [mem_union, mem_setOf_eq]
    omega
  calc
    π (vround δ ⁻¹' {v | |v - w| < r}) ≤ π ({v : ℝ | (⌊v / δb⌋ : ℤ) = c₀ - 1} ∪
        {v : ℝ | (⌊v / δb⌋ : ℤ) = c₀} ∪ {v : ℝ | (⌊v / δb⌋ : ℤ) = c₀ + 1}) := measure_mono hsub
    _ ≤ π {v : ℝ | (⌊v / δb⌋ : ℤ) = c₀ - 1} + π {v : ℝ | (⌊v / δb⌋ : ℤ) = c₀} +
        π {v : ℝ | (⌊v / δb⌋ : ℤ) = c₀ + 1} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ pcap + pcap + pcap := add_le_add (add_le_add (hcap _) (hcap _)) (hcap _)
    _ = 3 * pcap := by ring

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
