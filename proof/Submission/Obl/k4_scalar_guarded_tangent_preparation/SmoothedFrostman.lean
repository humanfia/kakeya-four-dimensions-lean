import Submission.Obl.k4_scalar_guarded_tangent_preparation.PaletteSmoothing
import Submission.Obl.k4_row_cell_regularization.Palette

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

/-- The fixed blur charges only a slightly enlarged interval under the
same original reference law. Its weights need not be recomputed later. -/
theorem scatterPalette_le_original_interval
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) (U : Ω → ι) (hU : Measurable U) (V : Ω → ℝ)
    (p center : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ i, ENNReal.ofReal (p i) = μ (U ⁻¹' {i}))
    (hclose : ∀ᵐ x ∂μ, |V x - center (U x)| ≤ δ) (a b : ℝ) :
    scatterPalette p center δ (Icc a b) ≤ μ (V ⁻¹' Icc (a - 3 * δ) (b + 3 * δ)) := by
  classical
  let s := Finset.univ.filter (fun i => center i ∈ Icc (a - 2 * δ) (b + 2 * δ))
  calc
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (p i) := scatterPalette_interval_upper p center hδ a b
    _ = μ (U ⁻¹' (s : Set ι)) := by
      simp_rw [hp]
      exact sum_measure_preimage_singleton s (fun i _ => hU (measurableSet_singleton i))
    _ ≤ _ := by
      apply measure_mono_ae
      filter_upwards [hclose] with x hx
      intro hxs
      have hsx := (Finset.mem_filter.mp hxs).2
      have hnear := abs_le.mp hx
      exact ⟨by linarith [hsx.1], by linarith [hsx.2]⟩

/-- An interval enlarged by at most two coarse widths is covered by six
original floor bins, including both possible endpoint atoms. -/
theorem enlarged_interval_le_six_bins
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (V : Ω → ℝ)
    {width a b : ℝ} (hwidth : 0 < width) (e : ℤ)
    (ha : ((e - 2 : ℤ) : ℝ) * width ≤ a)
    (hb : b ≤ ((e + 3 : ℤ) : ℝ) * width) (C : ℝ≥0∞)
    (hcap : ∀ j : ℤ, μ {x | (⌊V x / width⌋ : ℤ) = j} ≤ C) :
    μ (V ⁻¹' Icc a b) ≤ 6 * C := by
  classical
  let s := Finset.Icc (e - 2) (e + 3)
  have hcover : V ⁻¹' Icc a b ⊆ ⋃ j ∈ s, {x | (⌊V x / width⌋ : ℤ) = j} := by
    intro x hx
    have hlow : ((e - 2 : ℤ) : ℝ) ≤ V x / width :=
      (le_div_iff₀ hwidth).2 (ha.trans hx.1)
    have hhigh : V x / width ≤ ((e + 3 : ℤ) : ℝ) :=
      (div_le_iff₀ hwidth).2 (hx.2.trans hb)
    have hj : (⌊V x / width⌋ : ℤ) ∈ s := by
      rw [Finset.mem_Icc]
      exact ⟨Int.le_floor.mpr hlow,
        (Int.floor_le_floor hhigh).trans_eq (Int.floor_intCast _)⟩
    exact mem_iUnion₂.mpr ⟨_, hj, rfl⟩
  have hs : s.card = 6 := by
    rw [Int.card_Icc]
    have h : e + 3 + 1 - (e - 2) = (6 : ℤ) := by omega
    rw [h]
    rfl
  calc
    _ ≤ μ (⋃ j ∈ s, {x | (⌊V x / width⌋ : ℤ) = j}) := measure_mono hcover
    _ ≤ ∑ j ∈ s, μ {x | (⌊V x / width⌋ : ℤ) = j} := measure_biUnion_finset_le s _
    _ ≤ ∑ _j ∈ s, C := Finset.sum_le_sum (fun j _ => hcap j)
    _ = _ := by simp only [Finset.sum_const, hs, nsmul_eq_mul, Nat.cast_ofNat]

/-- Blurring a very fine velocity code preserves every coarse angular
floor-bin cap, with one absolute factor and the same original law. -/
theorem smoothed_floor_bin_cap
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) (U : Ω → ι) (hU : Measurable U) (V : Ω → ℝ)
    (p center : ι → ℝ) {δ width : ℝ} (hδ : 0 < δ) (hwidth : 2 * δ ≤ width)
    (hp : ∀ i, ENNReal.ofReal (p i) = μ (U ⁻¹' {i}))
    (hclose : ∀ᵐ x ∂μ, |V x - center (U x)| ≤ δ)
    (C : ℝ≥0∞)
    (hcap : ∀ j : ℤ, μ {x | (⌊V x / width⌋ : ℤ) = j} ≤ C) (e : ℤ) :
    scatterPalette p center δ {v | (⌊v / width⌋ : ℤ) = e} ≤ 6 * C := by
  have hw : 0 < width := by linarith
  rw [← Submission.Obl.k4_row_cell_regularization.velocityCell_eq_floor hw,
    Submission.Obl.k4_row_cell_regularization.velocityCell, scatterPalette_Ico_eq_Icc]
  apply (scatterPalette_le_original_interval μ U hU V p center hδ hp hclose _ _).trans
  apply enlarged_interval_le_six_bins μ V hw e ?_ ?_ C hcap
  · push_cast
    nlinarith
  · push_cast
    nlinarith

end Submission.Obl.k4_scalar_guarded_tangent_preparation
