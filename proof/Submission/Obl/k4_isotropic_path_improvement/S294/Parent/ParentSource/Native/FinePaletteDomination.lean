-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FinePaletteDomination, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FinePaletteDomination.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FinePaletteDomination.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FinePaletteDomination.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/FinePaletteDomination.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineRetention

/-! The normalized retained fine-state palette is dominated by the OLD
coarse palette. No retained reference marginal enters the original joint cap. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal

theorem countable_measure_le_of_singletons {Z : Type*} [MeasurableSpace Z]
    [Countable Z] [MeasurableSingletonClass Z] (μ ν : Measure Z)
    (h : ∀ z, μ {z} ≤ ν {z}) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro S _
  have hsum (ξ : Measure Z) : (∑' z : S, ξ {(z : Z)}) = ξ S := by
    simpa only [preimage_id] using tsum_measure_preimage_singleton (f := id) (μ := ξ)
      (Set.to_countable S) (fun z _ => measurableSet_singleton z)
  rw [← hsum μ, ← hsum ν]
  exact ENNReal.tsum_le_tsum (fun z => h z.val)

theorem retained_fine_palette_joint_cap {Ω E Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (U : Set Ω)
    (hcell : ∀ e, MeasurableSet {z | f z = e}) (hU : MeasurableSet U)
    (palette : Ω → Z) {A α : ℝ} (hA : 0 ≤ A) (hα : 0 < α)
    (e : E) (he : e ∉ fineRetentionFailures μ f U (ENNReal.ofReal α))
    (hcap : ∀ q, μ.real {z | z ∈ U ∧ f z = e ∧ palette z = q} ≤
      A * μ.real {z | f z = e} * μ.real {z | palette z = q}) (q : Z) :
    (ProbabilityTheory.cond μ {z | f z = e ∧ z ∈ U}).real {z | palette z = q} ≤
      (A / α) * μ.real {z | palette z = q} := by
  let F := {z | f z = e ∧ z ∈ U}
  have hF : MeasurableSet F := (hcell e).inter hU
  have hpos : 0 < μ.real {z | f z = e} :=
    ENNReal.toReal_pos (not_or.mp he).1 (measure_ne_top _ _)
  have hretained := fine_retention_floor_real μ f U e (hcell e) hα.le he
  have hFpos : 0 < μ.real F := (mul_pos hα hpos).trans_le hretained
  rw [cond_real_apply μ F hF]
  apply (div_le_iff₀ hFpos).mpr
  have hnum : μ.real (F ∩ {z | palette z = q}) =
      μ.real {z | z ∈ U ∧ f z = e ∧ palette z = q} := by
    congr 1
    ext z
    simp only [F, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [hnum]
  apply (hcap q).trans
  calc
    A * μ.real {z | f z = e} * μ.real {z | palette z = q} =
        ((A / α) * μ.real {z | palette z = q}) * (α * μ.real {z | f z = e}) := by
      field_simp
    _ ≤ ((A / α) * μ.real {z | palette z = q}) * μ.real F :=
      mul_le_mul_of_nonneg_left hretained (by positivity)

theorem retained_fine_palette_domination {Ω E Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [Countable Z] [MeasurableSingletonClass Z]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (U : Set Ω)
    (hcell : ∀ e, MeasurableSet {z | f z = e}) (hU : MeasurableSet U)
    (palette : Ω → Z) (hpalette : Measurable palette) {A α : ℝ} (hA : 0 ≤ A) (hα : 0 < α)
    (e : E) (he : e ∉ fineRetentionFailures μ f U (ENNReal.ofReal α))
    (hcap : ∀ q, μ.real {z | z ∈ U ∧ f z = e ∧ palette z = q} ≤
      A * μ.real {z | f z = e} * μ.real {z | palette z = q}) :
    (ProbabilityTheory.cond μ {z | f z = e ∧ z ∈ U}).map palette ≤
      ENNReal.ofReal (A / α) • μ.map palette := by
  apply countable_measure_le_of_singletons
  intro q
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hpalette (measurableSet_singleton q),
    Measure.map_apply hpalette (measurableSet_singleton q)]
  have hreal := retained_fine_palette_joint_cap μ f U hcell hU palette hA hα e he hcap q
  have hbound := ENNReal.ofReal_le_ofReal hreal
  simp only [measureReal_def] at hbound
  rw [ENNReal.ofReal_mul (div_nonneg hA hα.le), ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at hbound
  exact hbound

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
