import Submission.Obl.k4_scalar_guarded_tangent_preparation.VelocityReadout

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

/-- Fine-code correctness is needed only almost everywhere under the
current law. Later masks inherit this from the original reference law. -/
theorem joint_interval_from_fine_cells_ae
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ρ : Measure Ω) (Z : Ω → ι) (V : Ω → ℝ)
    (p center : ι → ℝ) {δ a b : ℝ} (hδ : 0 < δ) (hlength : 2 * δ ≤ b - a)
    (P : Set Ω) (C : ℝ≥0∞)
    (hclose : ∀ᵐ x ∂ρ, |V x - center (Z x)| ≤ δ)
    (hcap : ∀ i, ρ (P ∩ Z ⁻¹' {i}) ≤ C * ENNReal.ofReal (p i)) :
    ρ (P ∩ V ⁻¹' Ico a b) ≤ 4 * C * scatterPalette p center δ (Ico a b) := by
  let P' := P ∩ {x | |V x - center (Z x)| ≤ δ}
  have heq : P =ᵐ[ρ] P' := by
    filter_upwards [hclose] with x hx
    exact propext ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
  rw [measure_congr (ae_eq_set_inter heq Filter.EventuallyEq.rfl)]
  apply joint_interval_from_fine_cells ρ Z V p center hδ hlength P' C
    (fun _ hx => hx.2)
  intro i
  exact (measure_mono (inter_subset_inter_left _ inter_subset_left)).trans (hcap i)

theorem joint_floor_bin_from_fine_cells_ae
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ρ : Measure Ω) (Z : Ω → ι) (V : Ω → ℝ) (p center : ι → ℝ)
    {δ width : ℝ} (hδ : 0 < δ) (hwidth : 2 * δ ≤ width)
    (P : Set Ω) (C : ℝ≥0∞)
    (hclose : ∀ᵐ x ∂ρ, |V x - center (Z x)| ≤ δ)
    (hcap : ∀ i, ρ (P ∩ Z ⁻¹' {i}) ≤ C * ENNReal.ofReal (p i)) (e : ℤ) :
    ρ (P ∩ {x | (⌊V x / width⌋ : ℤ) = e}) ≤
      4 * C * scatterPalette p center δ {v | (⌊v / width⌋ : ℤ) = e} := by
  have hwidth0 : 0 < width := by linarith
  change ρ (P ∩ V ⁻¹' {v | (⌊v / width⌋ : ℤ) = e}) ≤ _
  rw [← Submission.Obl.k4_row_cell_regularization.velocityCell_eq_floor hwidth0]
  have hlength : 2 * δ ≤ ((e : ℝ) + 1) * width - (e : ℝ) * width := by nlinarith
  exact joint_interval_from_fine_cells_ae ρ Z V p center hδ hlength P C hclose hcap

end Submission.Obl.k4_scalar_guarded_tangent_preparation
