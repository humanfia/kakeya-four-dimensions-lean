/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PaletteCellMass.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.PaletteWeightedCounts

/-! Sum original affine-cell occupation ceilings using the original palette once. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem joint_palette_cell_mass_le {Ω P V : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (code : Ω → P × V) (F : Finset (P × V))
    (hcover : ∀ p ∈ E, code p ∈ F) (palette : V → ℝ≥0∞)
    (hpalette : (∑ c ∈ F.image Prod.snd, palette c) ≤ 1) (τ : ℝ≥0∞)
    (hcap : ∀ qc ∈ F, μ {p | p ∈ E ∧ code p = qc} ≤ τ * palette qc.2) :
    μ E ≤ τ * ((F.image Prod.fst).card : ℝ≥0∞) := by
  have hsub : E ⊆ ⋃ qc ∈ F, {p | p ∈ E ∧ code p = qc} := by
    intro p hp
    exact Set.mem_iUnion₂.mpr ⟨code p,hcover p hp,hp,rfl⟩
  calc
    _ ≤ ∑ qc ∈ F, μ {p | p ∈ E ∧ code p = qc} :=
      (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ qc ∈ F, τ * palette qc.2 := Finset.sum_le_sum hcap
    _ = τ * (∑ qc ∈ F, palette qc.2) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul' le_rfl (sum_pair_palette_weights_le F palette hpalette)

end Submission.Obl.k4_scalar_grid_parameter_preparation
