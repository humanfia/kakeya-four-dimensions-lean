-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.WholeStateBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/WholeStateBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/WholeStateBreadth.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/WholeStateBreadth.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_scalar_heavy_intercept_selection.BaseCap


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- A uniform original pencil ceiling survives every union of whole
fine states. Its complement gives the breadth needed by native base
filling, with no conditional renormalization or state-mass loss. -/
theorem breadth_of_whole_state_union {Ω Q : Type*} {n : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q) (hstate : Measurable state)
    (e : Ω → EuclideanSpace ℝ (Fin n)) (he : Measurable e)
    (ρ p : ℝ) (hp : 0 ≤ p)
    (hcap : ∀ q, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      Module.finrank ℝ V < n →
      μ {x | state x = q ∧ Metric.infDist (e x) (V : Set _) < ρ} ≤
        ENNReal.ofReal p * μ (state ⁻¹' {q}))
    (U : Set Q) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hV : Module.finrank ℝ V < n) :
    (1 - p) * (μ.restrict (state ⁻¹' U)).real univ ≤
      (μ.restrict (state ⁻¹' U)).real {x | ρ ≤ Metric.infDist (e x) (V : Set _)} := by
  let S : Set Ω := {x | Metric.infDist (e x) (V : Set _) < ρ}
  let σ := μ.restrict (state ⁻¹' U)
  have hS : MeasurableSet S := measurableSet_lt he.infDist measurable_const
  have hinside := Submission.Obl.k4_scalar_heavy_intercept_selection.state_union_event_cap
    μ state hstate S (ENNReal.ofReal p) (fun q => hcap q V hV) U
  have hset : σ S = μ {x | state x ∈ U ∧ x ∈ S} := by
    rw [Measure.restrict_apply hS]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, and_comm]
  have hcapσ : σ S ≤ ENNReal.ofReal p * σ univ := by
    simpa only [hset, σ, Measure.restrict_apply_univ] using hinside
  have hreal : σ.real S ≤ p * σ.real univ := by
    have hr := ENNReal.toReal_mono (by finiteness) hcapσ
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp] using hr
  have hsum := measureReal_add_measureReal_compl (μ := σ) hS
  have hcomp : Sᶜ = {x | ρ ≤ Metric.infDist (e x) (V : Set _)} := by
    ext x
    simp only [S, mem_compl_iff, mem_ofPred_eq, not_lt]
  rw [hcomp] at hsum
  change (1 - p) * σ.real univ ≤ _
  linarith

/-- Taking one actual strip and one assigned coarse base cell still
forms a union of whole ORIGINAL fine states. The same original pencil
ceiling therefore gives breadth inside that precise group-cell law. -/
theorem breadth_of_whole_group_cell {Ω Q I J : Type*} {n : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q) (hstate : Measurable state)
    (e : Ω → EuclideanSpace ℝ (Fin n)) (he : Measurable e)
    (ρ p : ℝ) (hp : 0 ≤ p)
    (hcap : ∀ q, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      Module.finrank ℝ V < n →
      μ {x | state x = q ∧ Metric.infDist (e x) (V : Set _) < ρ} ≤
        ENNReal.ofReal p * μ (state ⁻¹' {q}))
    (group : Q → I) (coarse : Q → J) (i : I) (j : J)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hV : Module.finrank ℝ V < n) :
    (1 - p) * ((μ.restrict {x | group (state x) = i}).restrict
      {x | coarse (state x) = j}).real univ ≤
      ((μ.restrict {x | group (state x) = i}).restrict {x | coarse (state x) = j}).real
        {x | ρ ≤ Metric.infDist (e x) (V : Set _)} := by
  let U : Set Q := {q | group q = i ∧ coarse q = j}
  have hcoarse : MeasurableSet {x | coarse (state x) = j} :=
    (Set.to_countable {q | coarse q = j}).measurableSet.preimage hstate
  have heq : (μ.restrict {x | group (state x) = i}).restrict {x | coarse (state x) = j} =
      μ.restrict (state ⁻¹' U) := by
    rw [Measure.restrict_restrict hcoarse]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, U, and_comm]
  rw [heq]
  exact breadth_of_whole_state_union μ state hstate e he ρ p hp hcap U V hV

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
