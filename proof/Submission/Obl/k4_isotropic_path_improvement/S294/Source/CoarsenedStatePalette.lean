-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.CoarsenedStatePalette, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordStates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalPaletteCoarsening

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.OriginalVelocityPalette
open scoped ENNReal

noncomputable section

/-- A final child may request its own coarser velocity mesh. The state
source and code are unchanged, breadth passes to the narrower strip,
and one probability palette derived from the original fine palette pays
only the four compatible coarser bins. -/
theorem StateClauses.coarsen_palette
    {Kfine K eps fineWidth width : ℝ} {ν : Measure Parent.Ln}
    {base : Parent.Ev → EuclideanSpace ℝ (Fin 3)} {signal : Parent.Ev → ℝ}
    {S : Set Parent.Ev} {state : Parent.Ev → ℕ} {finePalette : Measure (Fin 2 → ℤ)}
    (h : StateClauses Kfine eps fineWidth ν base signal S state finePalette)
    (hKfine : 0 < Kfine) (hfour : 4*Kfine ≤ K)
    (hfine : 0 < fineWidth) (hwidth : fineWidth ≤ width) :
    ∃ palette : Measure (Fin 2 → ℤ), StateClauses K eps width ν base signal S state palette := by
  obtain ⟨hS,hstate,hfinite,hfaith,hbreadth,hprob,hcaps⟩ := h
  letI := hprob
  obtain ⟨palette,hpalette,htransfer⟩ :=
    exists_coarsened_original_vector_palette (Ω := Parent.Ev) (State := ℕ)
      fineWidth width hfine hwidth finePalette
  have hvelocity : Measurable (fun z : Parent.Ev => fun j : Fin 2 => Parent.v z.1 j) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (PiLp.continuous_apply 2 _ j).measurable.comp
      ((show Continuous Parent.v by unfold Parent.v; fun_prop).measurable.comp measurable_fst)
  have hcoarse := htransfer ((ν.prod volume).restrict S) state hstate
    (fun z j => Parent.v z.1 j) hvelocity
    (fun j => ((ν.prod volume).restrict S) {z | state z=j}) (ENNReal.ofReal Kfine) hcaps
  have hK : Kfine ≤ K := by linarith
  have hstrip : K^(-100:ℝ) ≤ Kfine^(-100:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hKfine hK (by norm_num)
  have hcoefficient : (4:ENNReal)*ENNReal.ofReal Kfine ≤ ENNReal.ofReal K := by
    calc
      (4:ENNReal)*ENNReal.ofReal Kfine=ENNReal.ofReal (4*Kfine) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)]
        norm_num
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hfour
  refine ⟨palette,hS,hstate,hfinite,hfaith,?_,hpalette,?_⟩
  · intro j normal offset hnormal
    apply (measure_mono (show {z : Parent.Ev | state z=j ∧
        |Inner.inner ℝ normal (O204.Split.v z.1)-offset| ≤ K^(-100:ℝ)}⊆
        {z | state z=j ∧ |Inner.inner ℝ normal (O204.Split.v z.1)-offset| ≤ Kfine^(-100:ℝ)}
      from fun _ hz => ⟨hz.1,hz.2.trans hstrip⟩)).trans
    exact hbreadth j normal offset hnormal
  · intro j b
    exact (hcoarse j b).trans (mul_le_mul' (mul_le_mul' hcoefficient le_rfl) le_rfl)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
