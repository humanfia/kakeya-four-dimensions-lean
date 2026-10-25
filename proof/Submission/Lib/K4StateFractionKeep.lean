import Mathlib

/-!
# Keeping a set where it is a substantial fraction of its state

Let `state : Ω → I` be a countable measurable partition and `G` a measurable set. Keep `G` only
on the states where it carries at least a fraction `f` of the state's mass:

* the deleted part of `G` costs at most `f` times the mass of the states that `G` meets;
* any per-state ratio bound `μ (state = i, S) ≤ η μ (state = i)` (for instance a strip
  breadth bound) passes to the kept part with ratio `η / f`, on every state and on every
  union of states.

Typical use: a source has a tiny per-state strip ratio on states that mix two branches. The
part of one branch, kept where it holds a fraction `f` of its state, then has strip ratio at
most `η / f` without any new renewal.
-/

namespace Submission.Lib.K4StateFractionKeep

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I] [Countable I]
  [MeasurableSingletonClass I]

/-- The states where `G` holds at least the fraction `f`. -/
def goodStates (μ : Measure Ω) (state : Ω → I) (G : Set Ω) (f : ℝ≥0∞) : Set I :=
  {i | f * μ (state ⁻¹' {i}) ≤ μ (G ∩ state ⁻¹' {i})}

/-- The kept part of `G`. -/
def fractionKeep (μ : Measure Ω) (state : Ω → I) (G : Set Ω) (f : ℝ≥0∞) : Set Ω :=
  G ∩ state ⁻¹' goodStates μ state G f

theorem measurableSet_fractionKeep {μ : Measure Ω} {state : Ω → I} (hstate : Measurable state)
    {G : Set Ω} (hG : MeasurableSet G) (f : ℝ≥0∞) :
    MeasurableSet (fractionKeep μ state G f) :=
  hG.inter (hstate (Set.to_countable _).measurableSet)

/-- **The deletion cost.** -/
theorem measure_diff_fractionKeep_le (μ : Measure Ω) {state : Ω → I} (hstate : Measurable state)
    (G : Set Ω) (f : ℝ≥0∞) :
    μ (G \ fractionKeep μ state G f) ≤
      f * μ (state ⁻¹' {i | (G ∩ state ⁻¹' {i}).Nonempty}) := by
  classical
  let bad : Set I := {i | (G ∩ state ⁻¹' {i}).Nonempty ∧ i ∉ goodStates μ state G f}
  have hsub : G \ fractionKeep μ state G f ⊆ ⋃ i ∈ bad, G ∩ state ⁻¹' {i} := by
    intro x hx
    have hxG : x ∈ G := hx.1
    have hxbad : state x ∉ goodStates μ state G f := fun h => hx.2 ⟨hxG, h⟩
    exact mem_iUnion₂.mpr ⟨state x, ⟨⟨x, hxG, rfl⟩, hxbad⟩, hxG, rfl⟩
  have hfiber (i : I) : MeasurableSet (state ⁻¹' {i}) := hstate (measurableSet_singleton i)
  calc
    μ (G \ fractionKeep μ state G f) ≤ μ (⋃ i ∈ bad, G ∩ state ⁻¹' {i}) := measure_mono hsub
    _ ≤ ∑' i : bad, μ (G ∩ state ⁻¹' {(i : I)}) :=
        measure_biUnion_le μ (Set.to_countable bad) _
    _ ≤ ∑' i : bad, f * μ (state ⁻¹' {(i : I)}) := by
        apply ENNReal.tsum_le_tsum
        intro i
        exact (lt_of_not_ge i.2.2).le
    _ = f * ∑' i : bad, μ (state ⁻¹' {(i : I)}) := ENNReal.tsum_mul_left
    _ = f * μ (⋃ i ∈ bad, state ⁻¹' {i}) := by
        congr 1
        rw [measure_biUnion (Set.to_countable bad)]
        · intro i _ i' _ hii'
          exact Disjoint.preimage _ (Set.disjoint_singleton.mpr hii')
        · intro i _
          exact hfiber i
    _ ≤ f * μ (state ⁻¹' {i | (G ∩ state ⁻¹' {i}).Nonempty}) := by
        apply mul_le_mul' le_rfl (measure_mono _)
        intro x hx
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
        simp only [mem_preimage, mem_singleton_iff] at hxi
        simp only [mem_preimage, mem_setOf_eq]
        rw [hxi]
        exact hi.1

/-- **Ratios pass to the kept part**, on every state. -/
theorem fractionKeep_state_ratio (μ : Measure Ω) (state : Ω → I) (G : Set Ω) {f : ℝ≥0∞}
    (hf0 : f ≠ 0) (hftop : f ≠ ⊤) (S : Set Ω) (η : ℝ≥0∞)
    (hη : ∀ i, μ (state ⁻¹' {i} ∩ S) ≤ η * μ (state ⁻¹' {i})) (i : I) :
    μ (fractionKeep μ state G f ∩ state ⁻¹' {i} ∩ S) ≤
      (η / f) * μ (fractionKeep μ state G f ∩ state ⁻¹' {i}) := by
  by_cases hi : i ∈ goodStates μ state G f
  · have heq : fractionKeep μ state G f ∩ state ⁻¹' {i} = G ∩ state ⁻¹' {i} := by
      ext x
      simp only [fractionKeep, mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨⟨hxG, _⟩, hxi⟩
        exact ⟨hxG, hxi⟩
      · rintro ⟨hxG, hxi⟩
        exact ⟨⟨hxG, by rw [hxi]; exact hi⟩, hxi⟩
    rw [heq]
    calc
      μ (G ∩ state ⁻¹' {i} ∩ S) ≤ μ (state ⁻¹' {i} ∩ S) :=
          measure_mono (fun x hx => ⟨hx.1.2, hx.2⟩)
      _ ≤ η * μ (state ⁻¹' {i}) := hη i
      _ = (η / f) * (f * μ (state ⁻¹' {i})) := by
          rw [← mul_assoc, ENNReal.div_mul_cancel hf0 hftop]
      _ ≤ (η / f) * μ (G ∩ state ⁻¹' {i}) := mul_le_mul' le_rfl hi
  · have hempty : fractionKeep μ state G f ∩ state ⁻¹' {i} ∩ S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨⟨⟨_, hgood⟩, hxi⟩, _⟩ := hx
      simp only [mem_preimage, mem_singleton_iff] at hgood hxi
      rw [hxi] at hgood
      exact hi hgood
    rw [hempty, measure_empty]
    exact zero_le

/-- **Ratios pass to the kept part on any union of states.** -/
theorem fractionKeep_union_ratio (μ : Measure Ω) {state : Ω → I} (hstate : Measurable state)
    {G : Set Ω} (hG : MeasurableSet G) {f : ℝ≥0∞} (hf0 : f ≠ 0) (hftop : f ≠ ⊤)
    {S : Set Ω} (hS : MeasurableSet S) (η : ℝ≥0∞)
    (hη : ∀ i, μ (state ⁻¹' {i} ∩ S) ≤ η * μ (state ⁻¹' {i})) (L : Set I) :
    μ (fractionKeep μ state G f ∩ state ⁻¹' L ∩ S) ≤
      (η / f) * μ (fractionKeep μ state G f ∩ state ⁻¹' L) := by
  have hkeep := measurableSet_fractionKeep (μ := μ) hstate hG f
  have hfiber (i : I) : MeasurableSet (state ⁻¹' {i}) := hstate (measurableSet_singleton i)
  have hdisj : Pairwise (Function.onFun Disjoint fun i : L => state ⁻¹' {(i : I)}) := by
    intro i i' hii'
    exact Disjoint.preimage _ (Set.disjoint_singleton.mpr (fun h => hii' (Subtype.ext h)))
  have hunion (T : Set Ω) : T ∩ state ⁻¹' L = ⋃ i : L, T ∩ state ⁻¹' {(i : I)} := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_iUnion, mem_singleton_iff]
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨⟨state x, hxL⟩, hxT, rfl⟩
    · rintro ⟨i, hxT, hxi⟩
      exact ⟨hxT, by rw [hxi]; exact i.2⟩
  haveI : Countable L := Subtype.countable
  calc
    μ (fractionKeep μ state G f ∩ state ⁻¹' L ∩ S)
        = μ (⋃ i : L, fractionKeep μ state G f ∩ state ⁻¹' {(i : I)} ∩ S) := by
          congr 1
          rw [inter_right_comm, hunion]
          congr 1
          funext i
          rw [inter_right_comm]
    _ = ∑' i : L, μ (fractionKeep μ state G f ∩ state ⁻¹' {(i : I)} ∩ S) := by
          apply measure_iUnion
          · intro i i' hii'
            exact (((hdisj hii').mono_left inter_subset_right).mono_left inter_subset_left).mono_right
              (inter_subset_left.trans inter_subset_right)
          · intro i
            exact (hkeep.inter (hfiber _)).inter hS
    _ ≤ ∑' i : L, (η / f) * μ (fractionKeep μ state G f ∩ state ⁻¹' {(i : I)}) :=
          ENNReal.tsum_le_tsum (fun i => fractionKeep_state_ratio μ state G hf0 hftop S η hη i)
    _ = (η / f) * ∑' i : L, μ (fractionKeep μ state G f ∩ state ⁻¹' {(i : I)}) :=
          ENNReal.tsum_mul_left
    _ = (η / f) * μ (fractionKeep μ state G f ∩ state ⁻¹' L) := by
          congr 1
          rw [hunion]
          symm
          apply measure_iUnion
          · intro i i' hii'
            exact ((hdisj hii').mono_left inter_subset_right).mono_right inter_subset_right
          · intro i
            exact hkeep.inter (hfiber _)

end

end Submission.Lib.K4StateFractionKeep
