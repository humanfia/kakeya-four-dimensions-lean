-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.Jets2.VelocityPaletteCoarsening, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/Jets2/VelocityPaletteCoarsening.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 18a3db56eab47c441a364ba278c399c30491bda9,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/Jets2/VelocityPaletteCoarsening.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.ParameterCompatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.ListedPalette
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicParameterBins

/-! # One fine physical-velocity palette answers all coarser tests

The accepted compatible-grid lists have exactly four entries in two
velocity coordinates. Dividing their old weights by four therefore
gives a subprobability palette at every coarser parameter resolution.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

def velocityPaletteAt (fineWidth width : ℝ) (weight : (Fin 2 → ℤ) → ENNReal)
    (q : Fin 2 → ℤ) : ENNReal :=
  (4:ENNReal)⁻¹*listedPalette
    (Submission.Obl.k4_scalar_graph_residual_discovery.coarseGridList width fineWidth) weight q

/-- No dyadic alignment is required for the palette: each fine
velocity bin has only four compatible coarser bins. -/
theorem tsum_velocityPaletteAt_le_one (fineWidth width : ℝ)
    (weight : (Fin 2 → ℤ) → ENNReal) (hweight : (∑' q, weight q) ≤ 1) :
    (∑' q, velocityPaletteAt fineWidth width weight q) ≤ 1 := by
  have hmenu (q : Fin 2 → ℤ) :
      ((Submission.Obl.k4_scalar_graph_residual_discovery.coarseGridList width fineWidth q).card:ENNReal) ≤ 4 := by
    rw [Submission.Obl.k4_scalar_graph_residual_discovery.card_coarseGridList]
    norm_num
  have hh := (tsum_listedPalette_le
    (Submission.Obl.k4_scalar_graph_residual_discovery.coarseGridList width fineWidth) weight 4 hmenu).trans
      (mul_le_mul' le_rfl hweight)
  calc
    _ = (4:ENNReal)⁻¹*∑' q, listedPalette
        (Submission.Obl.k4_scalar_graph_residual_discovery.coarseGridList width fineWidth) weight q :=
      ENNReal.tsum_mul_left
    _ ≤ (4:ENNReal)⁻¹*(4*1) := mul_le_mul' le_rfl hh
    _ = _ := by
      rw [mul_one, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

theorem finite_sum_velocityPaletteAt_le_one (fineWidth width : ℝ)
    (weight : (Fin 2 → ℤ) → ENNReal) (hweight : (∑' q, weight q) ≤ 1)
    (F : Finset (Fin 2 → ℤ)) : (∑ q∈F, velocityPaletteAt fineWidth width weight q) ≤ 1 :=
  (ENNReal.sum_le_tsum F).trans (tsum_velocityPaletteAt_le_one fineWidth width weight hweight)

/-- The original fine-bin domination passes to every coarser physical
velocity test at cost four, under the SAME old state references. -/
theorem velocityPaletteAt_state_cap {Ω Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (V : Ω → Fin 2 → ℝ) (hV : Measurable V)
    {fineWidth width : ℝ} (hfine : 0 < fineWidth) (hwidth : fineWidth ≤ width)
    (weight : (Fin 2 → ℤ) → ENNReal) (reference : Q → ENNReal) (C : ENNReal)
    (hcap : ∀ q v, μ {z | state z=q ∧ parameterCode fineWidth (V z)=v} ≤
      C*reference q*weight v)
    (q : Q) (v : Fin 2 → ℤ) :
    μ {z | state z=q ∧ parameterCode width (V z)=v} ≤
      (4*C)*reference q*velocityPaletteAt fineWidth width weight v := by
  have hh := listed_palette_state_cap μ state hstate
    (fun z => parameterCode fineWidth (V z)) ((measurable_parameterCode fineWidth).comp hV)
    (fun z => parameterCode width (V z)) ((measurable_parameterCode width).comp hV)
    (Submission.Obl.k4_scalar_graph_residual_discovery.coarseGridList width fineWidth)
    (fun z => Submission.Obl.k4_scalar_graph_residual_discovery.cell_mem_coarseGridList hfine hwidth (V z))
    weight reference C hcap q v
  apply hh.trans_eq
  have hfour : (4:ENNReal)*(4:ENNReal)⁻¹=1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  dsimp only [velocityPaletteAt]
  calc
    _ = C*reference q*((4*(4:ENNReal)⁻¹)*listedPalette
        (Submission.Obl.k4_scalar_graph_residual_discovery.coarseGridList width fineWidth) weight v) := by
      rw [hfour,one_mul]
    _ = _ := by ring

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
