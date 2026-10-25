-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.CellBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/CellBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/CellBreadth.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit d78c43c7c261;
-- source Submission/Obl/k4_isotropic_path_improvement/CellBreadth.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CellRows

/-!
The physical velocity graph outside genuinely broad fine states. Every
loss is measured in the original incidence law, including the total mass
of states to which the four-dimensional Kakeya obstruction applies.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open MeasureTheory Set Module
open SourceGeometry
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

def cellBroad {m d : ℕ} (μ : Measure Ω) (code : Ω → Fin m)
    (e : Ω → EuclideanSpace ℝ (Fin d)) (ρ c : ℝ) (i : Fin m) : Prop :=
  ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), finrank ℝ V < d →
    c * (μ.restrict (code ⁻¹' {i})).real univ ≤
      (μ.restrict (code ⁻¹' {i})).real {x | ρ ≤ Metric.infDist (e x) (V : Set _)}

/-- Partitioning any later event still sums against the original cell laws. -/
theorem sum_real_restrict_code {m : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Fin m) (hcode : Measurable code) (S : Set Ω) (hS : MeasurableSet S) :
    (∑ i, (μ.restrict (code ⁻¹' {i})).real S) = μ.real S := by
  have h := sum_codeWeight (μ.restrict S) code hcode
  have heq (i : Fin m) : codeWeight (μ.restrict S) code i =
      (μ.restrict (code ⁻¹' {i})).real S := by
    simp only [codeWeight, measureReal_def, Measure.restrict_apply' hS,
      Measure.restrict_apply' (hcode (measurableSet_singleton i)), inter_comm]
  simp_rw [heq] at h
  simpa only [measureReal_def, Measure.restrict_apply_univ] using h

/-- Statewise capture loses only the original bad-state mass and the
prescribed fractional loss on the other original cell laws. -/
theorem select_reference_states {m : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Fin m) (hcode : Measurable code) (Broad : Fin m → Prop)
    (Q : Fin m → Set Ω) (hQ : ∀ i, MeasurableSet (Q i))
    (c : ℝ) (hc : 0 ≤ c)
    (hcost : ∀ i, ¬ Broad i → (μ.restrict (code ⁻¹' {i})).real (Q i)ᶜ ≤
      c * (μ.restrict (code ⁻¹' {i})).real univ) :
    ∃ T : Set Ω, MeasurableSet T ∧
      μ.real Tᶜ ≤ μ.real {x | Broad (code x)} + c * μ.real univ ∧
      ∀ x ∈ T, ¬ Broad (code x) ∧ x ∈ Q (code x) := by
  classical
  let laws (i : Fin m) := μ.restrict (code ⁻¹' {i})
  let R (i : Fin m) := if Broad i then ∅ else Q i
  have hR (i : Fin m) : MeasurableSet (R i) := by
    dsimp only [R]
    split_ifs
    · exact MeasurableSet.empty
    · exact hQ i
  let T := ⋃ i : Fin m, (code ⁻¹' {i}) ∩ R i
  have hT : MeasurableSet T := MeasurableSet.iUnion fun i =>
    (hcode (measurableSet_singleton i)).inter (hR i)
  have hmem (x : Ω) : x ∈ T ↔ x ∈ R (code x) := by
    constructor
    · intro hx
      obtain ⟨i, hxi, hxR⟩ := Set.mem_iUnion.mp hx
      have hxi : code x = i := hxi
      simpa only [hxi] using hxR
    · intro hx
      exact Set.mem_iUnion.mpr ⟨code x, by simp, hx⟩
  have hcell (i : Fin m) : (laws i).real Tᶜ ≤
      (if Broad i then (laws i).real univ else 0) + c * (laws i).real univ := by
    by_cases hi : Broad i
    · rw [ite_eq_left hi]
      exact (measureReal_mono (subset_univ _)).trans (le_add_of_nonneg_right (by positivity))
    · rw [ite_eq_right hi, zero_add]
      have hsub : Tᶜ ∩ code ⁻¹' {i} ⊆ (Q i)ᶜ ∩ code ⁻¹' {i} := by
        intro x hx
        refine ⟨?_, hx.2⟩
        intro hxQ
        apply hx.1
        apply (hmem x).mpr
        have hxi : code x = i := hx.2
        simpa only [hxi, R, ite_eq_right hi] using hxQ
      have hle : (laws i).real Tᶜ ≤ (laws i).real (Q i)ᶜ := by
        simp only [laws, measureReal_def, Measure.restrict_apply' (hcode (measurableSet_singleton i))]
        exact measureReal_mono hsub
      exact hle.trans (hcost i hi)
  have hbadsum : (∑ i, if Broad i then (laws i).real univ else 0) =
      μ.real {x | Broad (code x)} := by
    simpa only [laws, measureReal_def, Measure.restrict_apply_univ, codeWeight] using
      sum_codeWeight_predicate μ code hcode Broad
  refine ⟨T, hT, ?_, ?_⟩
  · rw [← sum_real_restrict_code μ code hcode Tᶜ hT.compl]
    calc
      _ ≤ ∑ i, ((if Broad i then (laws i).real univ else 0) + c * (laws i).real univ) :=
        Finset.sum_le_sum fun i _ => hcell i
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          sum_real_restrict_code μ code hcode univ MeasurableSet.univ, hbadsum]
  · intro x hx
    have hxR := (hmem x).mp hx
    have hn : ¬ Broad (code x) := by
      intro hi
      simp only [R, ite_eq_left hi, mem_empty_iff_false] at hxR
    exact ⟨hn, by simpa only [R, ite_eq_right hn] using hxR⟩


end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
