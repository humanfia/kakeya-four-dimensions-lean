import Mathlib

/-!
Adapted from: here:o114 (session x0383), BadFibers.lean and ListedExceptions.lean.

Original product-law bounds for exceptional fibers and eligible observed
witness lists, together with finite base-sublevel deletion and weighted density
budgets. The laws remain unnormalized throughout.
-/

namespace Submission.Lib.K4ListedExceptions

open Set MeasureTheory
open scoped ENNReal

/-- The failure budget splits into the bad-anchor mass and the uniform
bad-detour mass on each remaining anchor fiber. -/
theorem prod_measure_le_of_bad_fibers {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (A B : Set X) (D : Set Y) (E : Set (X × Y))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hsub : E ⊆ A ×ˢ D) {ε : ENNReal}
    (hgood : ∀ x ∈ A, x ∉ B → ν (Prod.mk x ⁻¹' E) ≤ ε) :
    (μ.prod ν) E ≤ ν D * μ B + ε * μ A := by
  classical
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ x, B.indicator (fun _ => ν D) x + A.indicator (fun _ => ε) x ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      by_cases hxA : x ∈ A
      · by_cases hxB : x ∈ B
        · rw [indicator_of_mem hxA, indicator_of_mem hxB]
          apply le_trans (measure_mono ?_) (le_add_right le_rfl)
          intro y hy
          exact (hsub hy).2
        · rw [indicator_of_mem hxA, indicator_of_notMem hxB, zero_add]
          exact hgood x hxA hxB
      · have hf : Prod.mk x ⁻¹' E = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hxA (hsub hy).1
        rw [hf, measure_empty]
        exact zero_le
    _ = ν D * μ B + ε * μ A := by
      rw [lintegral_add_left (measurable_const.indicator hB),
        lintegral_indicator_const hB, lintegral_indicator_const hA]


/-- Remove parameters that fail for any eligible witness in the observed list. -/
def listedBadEvent {X Θ ι : Type*} (S : Set X) (L : X → Finset ι)
    (eligible : ι → X → Prop) (Bad : ι → Set (X × Θ)) : Set (X × Θ) :=
  {p | p.1 ∈ S ∧ ∃ i ∈ L p.1, eligible i p.1 ∧ p ∈ Bad i}

theorem measurableSet_listedBadEvent {X Θ ι : Type*}
    [MeasurableSpace X] [MeasurableSpace Θ] [Fintype ι]
    (S : Set X) (L : X → Finset ι) (eligible : ι → X → Prop) (Bad : ι → Set (X × Θ))
    (hS : MeasurableSet S) (hL : ∀ i, MeasurableSet {x | i ∈ L x})
    (heligible : ∀ i, MeasurableSet {x | eligible i x})
    (hBad : ∀ i, MeasurableSet (Bad i)) :
    MeasurableSet (listedBadEvent S L eligible Bad) := by
  have heq : listedBadEvent S L eligible Bad =
      ⋃ i, {p | p.1 ∈ S ∧ i ∈ L p.1 ∧ eligible i p.1 ∧ p ∈ Bad i} := by
    ext p
    simp only [listedBadEvent, mem_setOf_eq, mem_iUnion]
    aesop
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  exact (hS.preimage measurable_fst).inter ((hL i).preimage measurable_fst |>.inter
    ((heligible i).preimage measurable_fst |>.inter (hBad i)))

/-- Uniform exceptional fibers and a bounded observed list give a relative
exception bound in the original product law. -/
theorem measure_listedBadEvent_le {X Θ ι : Type*}
    [MeasurableSpace X] [MeasurableSpace Θ] [Fintype ι]
    (μ : Measure X) (π : Measure Θ) [SFinite π]
    (S : Set X) (L : X → Finset ι) (eligible : ι → X → Prop) (Bad : ι → Set (X × Θ))
    (hS : MeasurableSet S) (hL : ∀ i, MeasurableSet {x | i ∈ L x})
    (heligible : ∀ i, MeasurableSet {x | eligible i x})
    (hBad : ∀ i, MeasurableSet (Bad i))
    {K ε : ℝ≥0∞} (hcard : ∀ x ∈ S, ((L x).card : ℝ≥0∞) ≤ K)
    (hfiber : ∀ x ∈ S, ∀ i ∈ L x, eligible i x → π (Prod.mk x ⁻¹' Bad i) ≤ ε) :
    (μ.prod π) (listedBadEvent S L eligible Bad) ≤ (K*ε) * μ S := by
  classical
  let E := listedBadEvent S L eligible Bad
  have hE := measurableSet_listedBadEvent S L eligible Bad hS hL heligible hBad
  have hbound (x : X) (hx : x ∈ S) : π (Prod.mk x ⁻¹' E) ≤ K*ε := by
    let U (i : {i // i ∈ L x}) : Set Θ :=
      if eligible i.val x then Prod.mk x ⁻¹' Bad i.val else ∅
    have hsub : Prod.mk x ⁻¹' E ⊆ ⋃ i, U i := by
      intro θ hθ
      obtain ⟨_,i,hi,he,hb⟩ := hθ
      exact mem_iUnion.mpr ⟨⟨i,hi⟩, by simpa only [U, if_pos he, mem_preimage] using hb⟩
    calc
      π (Prod.mk x ⁻¹' E) ≤ π (⋃ i, U i) := measure_mono hsub
      _ ≤ ∑ i, π (U i) := measure_iUnion_fintype_le π _
      _ ≤ ∑ _i : {i // i ∈ L x}, ε := by
        apply Finset.sum_le_sum
        intro i _
        by_cases he : eligible i.val x
        · simpa only [U, if_pos he] using hfiber x hx i.val i.property he
        · simp only [U, if_neg he, measure_empty]
          exact zero_le
      _ = ((L x).card : ℝ≥0∞) * ε := by simp [nsmul_eq_mul]
      _ ≤ K*ε := by gcongr; exact hcard x hx
  have hsub : E ⊆ S ×ˢ (univ : Set Θ) := fun _ hp => ⟨hp.1, mem_univ _⟩
  have h := prod_measure_le_of_bad_fibers μ π S ∅ univ E hS MeasurableSet.empty hE hsub
    (fun x hx _ => hbound x hx)
  simpa only [measure_empty, mul_zero, zero_add] using h

/-- A finite collection of exceptional base sets is charged to the same original
base-density ceiling. The law is not renormalized after deletion. -/
theorem finite_base_exception_bound {X Y ι : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    (S : Set X) (Z : X → Y) (L : Finset ι) (Bad : ι → Set Y)
    (hBad : ∀ i ∈ L, MeasurableSet (Bad i)) {c β ε : ℝ≥0∞}
    (hdom : ∀ U : Set Y, MeasurableSet U → c * μ (S ∩ Z ⁻¹' U) ≤ β * ν U)
    (hvol : ∀ i ∈ L, ν (Bad i) ≤ ε) :
    c * μ (S ∩ {x | ∃ i ∈ L, Z x ∈ Bad i}) ≤ β * ((L.card : ℝ≥0∞) * ε) := by
  classical
  let U : Set Y := ⋃ i : {i // i ∈ L}, Bad i.val
  have hU : MeasurableSet U := MeasurableSet.iUnion fun i => hBad i.val i.property
  have hUvol : ν U ≤ (L.card : ℝ≥0∞) * ε := by
    calc
      ν U ≤ ∑ i : {i // i ∈ L}, ν (Bad i.val) := measure_iUnion_fintype_le ν _
      _ ≤ ∑ _i : {i // i ∈ L}, ε :=
        Finset.sum_le_sum fun i _ => hvol i.val i.property
      _ = _ := by simp [nsmul_eq_mul]
  have heq : S ∩ {x | ∃ i ∈ L, Z x ∈ Bad i} = S ∩ Z ⁻¹' U := by
    ext x
    simp [U]
  rw [heq]
  exact (hdom U hU).trans (by gcongr)

/-- Original weighted density budgets sum the entrywise exception bounds,
including any coarse-time factors already placed in the weights and ceilings. -/
theorem weighted_exception_budget {ι : Type*} [Fintype ι]
    (ω c β bad : ι → ℝ≥0∞) {K ε B : ℝ≥0∞}
    (hentry : ∀ i, c i * bad i ≤ β i * (K*ε))
    (hbudget : ∑ i, ω i * β i ≤ B) :
    ∑ i, ω i * c i * bad i ≤ (K*ε) * B := by
  calc
    (∑ i, ω i * c i * bad i) = ∑ i, ω i * (c i * bad i) := by simp only [mul_assoc]
    _ ≤ ∑ i, ω i * (β i * (K*ε)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul le_rfl (hentry i) zero_le zero_le
    _ = (K*ε) * ∑ i, ω i * β i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
    _ ≤ (K*ε) * B := by gcongr


end Submission.Lib.K4ListedExceptions
