-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FineRetention, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FineRetention.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FineRetention.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FineRetention.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/FineRetention.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeBroadSelection

/-! Retained-fine-state thresholds are charged to the OLD fine marginal,
with one countable partition bound and no number-of-states factor. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal

noncomputable def fineRetentionFailures {Ω Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : Ω → Z) (U : Set Ω) (α : ENNReal) : Set Z :=
  {e | μ (q ⁻¹' {e}) = 0 ∨ ¬ α * μ (q ⁻¹' {e}) ≤ (μ.restrict U) (q ⁻¹' {e})}

theorem fine_retention_failures_mass_le {Ω Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [Countable Z] [MeasurableSingletonClass Z]
    (μ : Measure Ω) (q : Ω → Z) (hq : Measurable q) (U : Set Ω) (α : ENNReal) :
    μ (U ∩ q ⁻¹' fineRetentionFailures μ q U α) ≤ α * μ univ := by
  classical
  let Bad := fineRetentionFailures μ q U α
  have hBad : MeasurableSet (q ⁻¹' Bad) := hq ((Set.to_countable Bad).measurableSet)
  have hsum (ξ : Measure Ω) : (∑' e : Bad, ξ (q ⁻¹' {(e : Z)})) = ξ (q ⁻¹' Bad) :=
    tsum_measure_preimage_singleton (Set.to_countable Bad)
      (fun e _ => (measurableSet_singleton e).preimage hq)
  calc
    _ = (μ.restrict U) (q ⁻¹' Bad) := by
      rw [Measure.restrict_apply hBad, inter_comm]
    _ = ∑' e : Bad, (μ.restrict U) (q ⁻¹' {(e : Z)}) := (hsum _).symm
    _ ≤ ∑' e : Bad, α * μ (q ⁻¹' {(e : Z)}) := by
      apply ENNReal.tsum_le_tsum
      intro e
      rcases e.property with hz | hlight
      · have hm : (μ.restrict U) (q ⁻¹' {(e : Z)}) ≤ μ (q ⁻¹' {(e : Z)}) := by
          rw [Measure.restrict_apply ((measurableSet_singleton _).preimage hq)]
          exact measure_mono inter_subset_left
        simpa only [hz, mul_zero] using hm
      · exact (lt_of_not_ge hlight).le
    _ = α * μ (q ⁻¹' Bad) := by rw [ENNReal.tsum_mul_left, hsum]
    _ ≤ _ := mul_le_mul le_rfl (measure_mono (subset_univ _)) zero_le zero_le

theorem fine_retention_floor_real {Ω Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (q : Ω → Z) (U : Set Ω)
    (e : Z) (hcell : MeasurableSet (q ⁻¹' {e})) {α : ℝ} (hα : 0 ≤ α)
    (he : e ∉ fineRetentionFailures μ q U (ENNReal.ofReal α)) :
    α * μ.real {z | q z = e} ≤ μ.real {z | q z = e ∧ z ∈ U} := by
  have hfloor : ENNReal.ofReal α * μ (q ⁻¹' {e}) ≤ (μ.restrict U) (q ⁻¹' {e}) :=
    not_not.mp (not_or.mp he).2
  have hr := ENNReal.toReal_mono (measure_ne_top (μ.restrict U) _) hfloor
  rw [Measure.restrict_apply hcell, ENNReal.toReal_mul, ENNReal.toReal_ofReal hα] at hr
  exact hr

theorem broad_selected_state_of_retention {Ω Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (q : Ω → Z) (U : Set Ω)
    (hcell : ∀ e, MeasurableSet {z | q z = e}) (hU : MeasurableSet U)
    (V : Ω → StripSpace) (r fraction α : ℝ) (hα : 0 < α) (hfraction : 0 ≤ fraction)
    (e : Z) (he : e ∉ narrowFineStates μ q U V r fraction)
    (hretained : e ∉ fineRetentionFailures μ q U (ENNReal.ofReal α)) :
    IsProbabilityMeasure (ProbabilityTheory.cond μ {z | q z = e ∧ z ∈ U}) ∧
      ∀ (n : StripSpace) (β : ℝ), ‖n‖ = 1 →
        (ProbabilityTheory.cond μ {z | q z = e ∧ z ∈ U}).real
          {z | V z ∈ affineStrip n β r} < fraction / α := by
  have hpos : 0 < μ.real {z | q z = e} :=
    ENNReal.toReal_pos (not_or.mp hretained).1 (measure_ne_top _ _)
  exact selected_fine_state_breadth μ q U hcell hU V r fraction α hα hfraction e hpos he
    (fine_retention_floor_real μ q U e (hcell e) hα.le hretained)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
