-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Kernels.PairConsensus; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Adapted from this LOT tree: obligation o247 (k4_wide_common_field_velocity_lists), branch x0870, commit e81b750b34aa9824cd7568c0d87d020832257f81, file Submission/Obl/k4_wide_common_field_velocity_lists/PairConsensus.lean (session x0870's work). -/
/- Port note: `real_code_table`, `stateEntryWeight` and `measurable_state_consensus` are
used from the accepted library `Submission.Lib.K4OriginalStatePreparation` (imported through
`MeasuredConsensus`), as the source file did through its abbreviations. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Kernels.StateResampling
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Kernels.MeasuredConsensus
import Mathlib.Algebra.BigOperators.Field

namespace Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels

open MeasureTheory Set Finset
open scoped Classical
open Submission.Lib.K4OriginalStatePreparation (real_code_table stateEntryWeight
  measurable_state_consensus)

noncomputable section

/-- The conditional finite table used for consensus is exactly the mass
of disagreement under the original full-incidence conditional redraw. -/
theorem statePair_disagreement_real {Ω Q ι : Type*} [MeasurableSpace Ω]
    [Fintype Q] [Fintype ι]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q) (entry : Ω → ι)
    (hs : Measurable state) (hi : Measurable entry) (R : Q → ι → ι → Prop) :
    (statePair μ state).real {p | ¬R (state p.1) (entry p.1) (entry p.2)} =
      ∑ q, (∑ j, stateEntryWeight μ state entry q j *
        ∑ i, if R q i j then 0 else stateEntryWeight μ state entry q i) /
          μ.real (state ⁻¹' {q}) := by
  classical
  have hstates (q : Q) : MeasurableSet (state ⁻¹' {q}) := hs (measurableSet_singleton q)
  letI := statePair_finite μ state hstates
  let code : Ω × Ω → Q × (ι × ι) :=
    fun p => (state p.1, entry p.1, entry p.2)
  have hc : Measurable code :=
    (hs.comp measurable_fst).prodMk
      ((hi.comp measurable_fst).prodMk (hi.comp measurable_snd))
  have hcell (q : Q) (i j : ι) :
      (statePair μ state).real (code ⁻¹' {(q, i, j)}) =
        stateEntryWeight μ state entry q i * stateEntryWeight μ state entry q j /
          μ.real (state ⁻¹' {q}) := by
    have heq : code ⁻¹' {(q, i, j)} =
        {p | state p = q ∧ entry p = i} ×ˢ (entry ⁻¹' {j}) := by
      ext p
      simp only [code, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_prod,
        Set.mem_ofPred_eq]
      tauto
    have hE : MeasurableSet {p | state p = q ∧ entry p = i} :=
      (hstates q).inter (hi (measurableSet_singleton i))
    rw [heq, statePair_fiber_rectangle_real μ state hstates q
      {p | state p = q ∧ entry p = i} (entry ⁻¹' {j}) hE
      (hi (measurableSet_singleton j)) (fun p hp => hp.1)]
    have hevent : (entry ⁻¹' {j}) ∩ state ⁻¹' {q} =
        {p | state p = q ∧ entry p = j} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_ofPred_eq]
      exact and_comm
    rw [hevent]
    rfl
  have h := real_code_table (statePair μ state) code hc
    (fun a : Q × (ι × ι) => ¬R a.1 a.2.1 a.2.2)
  rw [← h]
  simp only [Fintype.sum_prod_type, hcell]
  apply sum_congr rfl
  intro q _
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro j _
  rw [mul_sum, sum_div]
  apply sum_congr rfl
  intro i _
  by_cases hR : R q i j <;> simp [hR] <;> ring

/-- A bound for the literal pair experiment directly gives a measurable
deterministic consensus, retaining half of each occupied original state. -/
theorem measurable_consensus_of_pair_mass {Ω Q ι : Type*} [MeasurableSpace Ω]
    [Fintype Q] [Fintype ι] [Nonempty ι]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q) (entry : Ω → ι)
    (hs : Measurable state) (hi : Measurable entry) (R : Q → ι → ι → Prop) :
    ∃ (center : Q → ι) (H : Set Ω), MeasurableSet H ∧
      (∀ p ∈ H, R (state p) (entry p) (center (state p))) ∧
      (∀ q, μ.real (H ∩ state ⁻¹' {q}) = 0 ∨
        μ.real (state ⁻¹' {q}) / 2 ≤ μ.real (H ∩ state ⁻¹' {q})) ∧
      μ.real univ ≤ μ.real H +
        2 * (statePair μ state).real
          {p | ¬R (state p.1) (entry p.1) (entry p.2)} := by
  rw [statePair_disagreement_real μ state entry hs hi R]
  exact measurable_state_consensus μ state entry hs hi R

end

end Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels
