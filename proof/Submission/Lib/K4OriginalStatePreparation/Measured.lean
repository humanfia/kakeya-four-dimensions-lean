/- Adapted from: here:o247 (session x0870, original proofs in commits
4fa3d421, 60e815aa, 71be63c4, and 30be2d73). -/
import Submission.Lib.K4OriginalStatePreparation.Consensus
import Mathlib.MeasureTheory.Measure.Real

namespace Submission.Lib.K4OriginalStatePreparation

open MeasureTheory Set Finset

noncomputable section

open scoped Classical

/-- Summing an original finite code table recovers the measure of any
selection made using that table. -/
theorem real_code_table {Ω J : Type*} [MeasurableSpace Ω]
    [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → J) (hc : Measurable code)
    (P : J → Prop) [DecidablePred P] :
    (∑ j, if P j then μ.real (code ⁻¹' {j}) else 0) = μ.real {p | P (code p)} := by
  classical
  have h := sum_measureReal_preimage_singleton (μ := μ) (univ.filter P)
    (fun j _ => hc (measurableSet_singleton j))
  simpa [Finset.sum_filter] using h

/-- The unchanged real weights of a state/entry table. -/
def stateEntryWeight {Ω Q ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (state : Ω → Q) (entry : Ω → ι) (q : Q) (i : ι) : ℝ :=
  μ.real {p | state p = q ∧ entry p = i}

/-- Finite-state consensus is a measurable restriction of the actual law,
with a loss charged to the original conditional pair table. -/
theorem measurable_state_consensus {Ω Q ι : Type*} [MeasurableSpace Ω]
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
        2 * ∑ q, (∑ j, stateEntryWeight μ state entry q j *
          ∑ i, if R q i j then 0 else stateEntryWeight μ state entry q i) /
            μ.real (state ⁻¹' {q}) := by
  classical
  let w := stateEntryWeight μ state entry
  have hw (q : Q) (i : ι) : 0 ≤ w q i := measureReal_nonneg
  obtain ⟨center, keep, hrel, hhalf, _, hmass⟩ := state_consensus w R hw
  let H : Set Ω := {p | keep (state p) (entry p)}
  have hH : MeasurableSet H := by
    have hset : MeasurableSet {a : Q × ι | keep a.1 a.2} :=
      (Set.to_countable _).measurableSet
    exact hset.preimage (hs.prodMk hi)
  have htable (P : Q → ι → Prop) [∀ q i, Decidable (P q i)] :
      (∑ q, ∑ i, if P q i then w q i else 0) =
        μ.real {p | P (state p) (entry p)} := by
    have h := real_code_table μ (fun p => (state p, entry p)) (hs.prodMk hi)
      (fun a : Q × ι => P a.1 a.2)
    simpa only [Fintype.sum_prod_type, w, stateEntryWeight, Set.preimage,
      Set.mem_singleton_iff, Prod.mk.injEq] using h
  have hstate (q : Q) : (∑ i, w q i) = μ.real (state ⁻¹' {q}) := by
    have h := htable (fun r _ => r = q)
    simpa only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Set.preimage, Set.mem_singleton_iff] using h
  have hret (q : Q) : (∑ i, if keep q i then w q i else 0) =
      μ.real (H ∩ state ⁻¹' {q}) := by
    have h := htable (fun r i => r = q ∧ keep r i)
    have h' : (∑ i, if keep q i then w q i else 0) =
        μ.real {p | state p = q ∧ keep (state p) (entry p)} := by
      have hcollapse : (∑ r, ∑ i, if r = q ∧ keep r i then w r i else 0) =
          ∑ i, if keep q i then w q i else 0 := by
        rw [Finset.sum_eq_single q]
        · apply Finset.sum_congr rfl
          intro i _
          by_cases hi : keep q i <;> simp [hi]
        · intro r _ hr
          simp [hr]
        · simp
      exact hcollapse.symm.trans h
    convert h' using 1
    congr 1
    ext p
    simp only [H, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact and_comm
  refine ⟨center, H, hH, fun p hp => hrel _ _ hp, ?_, ?_⟩
  · intro q
    simpa only [hstate q, hret q] using hhalf q
  · have hall : (∑ q, ∑ i, w q i) = μ.real univ := by
      simpa using htable (fun _ _ => True)
    have hkeep : (∑ q, ∑ i, if keep q i then w q i else 0) = μ.real H :=
      htable keep
    rw [hall, hkeep] at hmass
    simpa only [hstate] using hmass

end

end Submission.Lib.K4OriginalStatePreparation
