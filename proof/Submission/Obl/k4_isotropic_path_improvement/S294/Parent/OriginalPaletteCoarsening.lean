-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.OriginalPaletteCoarsening, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalPaletteVector
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.VelocityPaletteCoarsening
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ProbabilityPaletteExtension

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette

open Set MeasureTheory
open ParentSource.Broad.Source.Jets2
open Qualification.Jets2
open scoped ENNReal

noncomputable section

/-- A probability palette fixed from the original fine bins answers
ANY one coarser velocity width, including nonaligned widths. The factor
four is paid once, with every original state reference unchanged. -/
theorem exists_coarsened_original_vector_palette
    {Ω State : Type*} [MeasurableSpace Ω]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (fineWidth width : ℝ) (hfine : 0 < fineWidth) (hwidth : fineWidth ≤ width)
    (finePalette : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure finePalette] :
    ∃ palette : Measure (Fin 2 → ℤ), IsProbabilityMeasure palette ∧
      ∀ (μ : Measure Ω) (state : Ω → State), Measurable state →
      ∀ (velocity : Ω → Fin 2 → ℝ), Measurable velocity →
      ∀ (reference : State → ENNReal) (C : ENNReal),
        (∀ q b, μ {z | state z=q ∧ (fun j => ⌊velocity z j/fineWidth⌋)=b} ≤
          C*reference q*finePalette {b}) →
        ∀ q b, μ {z | state z=q ∧ (fun j => ⌊velocity z j/width⌋)=b} ≤
          (4*C)*reference q*palette {b} := by
  let weights := fun b : Fin 2 → ℤ => finePalette {b}
  have hweight : (∑' b, weights b) ≤ 1 := by
    have hh := tsum_measure_preimage_singleton (μ := finePalette) (f := id)
      (Set.to_countable (univ : Set (Fin 2 → ℤ))) (fun b _ => measurableSet_singleton b)
    calc
      (∑' b, weights b) = ∑' b : (univ : Set (Fin 2 → ℤ)), weights b := (tsum_univ weights).symm
      _ ≤ 1 := by simpa only [weights,Set.preimage_id_eq,id_eq,measure_univ] using hh.le
  obtain ⟨palette,hprob,_hdom,hpoint⟩ := exists_probability_palette_dominating_weights
    (0 : Fin 2 → ℤ) (velocityPaletteAt fineWidth width weights)
    (tsum_velocityPaletteAt_le_one fineWidth width weights hweight)
  refine ⟨palette,hprob,?_⟩
  intro μ state hstate velocity hvelocity reference C hcap q b
  exact (velocityPaletteAt_state_cap μ state hstate velocity hvelocity hfine hwidth weights
    reference C hcap q b).trans (mul_le_mul' le_rfl (hpoint b))

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
