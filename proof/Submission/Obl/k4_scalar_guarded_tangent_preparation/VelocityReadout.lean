import Submission.Obl.k4_scalar_guarded_tangent_preparation.PaletteSmoothing
import Submission.Obl.k4_row_cell_regularization.Palette

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

/-- Fine velocity-cell joint ceilings imply joint ceilings on every
coarse interval. The single fixed blurred reference palette pays for
partial boundary cells, independently of the later incidence mask. -/
theorem joint_interval_from_fine_cells
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ρ : Measure Ω) (Z : Ω → ι) (V : Ω → ℝ)
    (p center : ι → ℝ) {δ a b : ℝ} (hδ : 0 < δ) (hlength : 2 * δ ≤ b - a)
    (P : Set Ω) (C : ℝ≥0∞)
    (hclose : ∀ x ∈ P, |V x - center (Z x)| ≤ δ)
    (hcap : ∀ i, ρ (P ∩ Z ⁻¹' {i}) ≤ C * ENNReal.ofReal (p i)) :
    ρ (P ∩ V ⁻¹' Ico a b) ≤ 4 * C * scatterPalette p center δ (Ico a b) := by
  classical
  let s := Finset.univ.filter (fun i => center i ∈ Icc (a - δ) (b + δ))
  have hcover : P ∩ V ⁻¹' Ico a b ⊆ ⋃ i ∈ s, P ∩ Z ⁻¹' {i} := by
    rintro x ⟨hxP, hxI⟩
    have hnear := abs_le.mp (hclose x hxP)
    have hcenter : center (Z x) ∈ Icc (a - δ) (b + δ) :=
      ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
    exact Set.mem_iUnion₂.mpr ⟨Z x, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hcenter⟩, hxP, rfl⟩
  have hpalette : (∑ i ∈ s, ENNReal.ofReal (p i)) ≤
      4 * scatterPalette p center δ (Ico a b) :=
    old_palette_cells_le_four_smoothed p center hδ hlength s
      (fun i hi => (Finset.mem_filter.mp hi).2)
  calc
    _ ≤ ρ (⋃ i ∈ s, P ∩ Z ⁻¹' {i}) := measure_mono hcover
    _ ≤ ∑ i ∈ s, ρ (P ∩ Z ⁻¹' {i}) := measure_biUnion_finset_le s _
    _ ≤ ∑ i ∈ s, C * ENNReal.ofReal (p i) := Finset.sum_le_sum (fun i _ => hcap i)
    _ = C * ∑ i ∈ s, ENNReal.ofReal (p i) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (4 * scatterPalette p center δ (Ico a b)) :=
      mul_le_mul le_rfl hpalette bot_le bot_le
    _ = _ := by ring

/-- The readout at a literal floor bin, valid for every width at least
twice the fixed fine velocity mesh. -/
theorem joint_floor_bin_from_fine_cells
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ρ : Measure Ω) (Z : Ω → ι) (V : Ω → ℝ) (p center : ι → ℝ)
    {δ width : ℝ} (hδ : 0 < δ) (hwidth : 2 * δ ≤ width)
    (P : Set Ω) (C : ℝ≥0∞)
    (hclose : ∀ x ∈ P, |V x - center (Z x)| ≤ δ)
    (hcap : ∀ i, ρ (P ∩ Z ⁻¹' {i}) ≤ C * ENNReal.ofReal (p i)) (e : ℤ) :
    ρ (P ∩ {x | (⌊V x / width⌋ : ℤ) = e}) ≤
      4 * C * scatterPalette p center δ {v | (⌊v / width⌋ : ℤ) = e} := by
  have hwidth0 : 0 < width := by linarith
  change ρ (P ∩ V ⁻¹' {v | (⌊v / width⌋ : ℤ) = e}) ≤ _
  rw [← Submission.Obl.k4_row_cell_regularization.velocityCell_eq_floor hwidth0]
  have hlength : 2 * δ ≤ ((e : ℝ) + 1) * width - (e : ℝ) * width := by nlinarith
  exact joint_interval_from_fine_cells ρ Z V p center hδ hlength P C hclose hcap

end Submission.Obl.k4_scalar_guarded_tangent_preparation
