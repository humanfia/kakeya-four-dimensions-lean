-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.PairMass; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254, session x0900, on the kernels of Field/Kernels/StateResampling.lean
and AgreementPairs.lean (ported from o247/x0870). -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Kernels.AgreementPairs

/-!
# Pair-disagreement mass from a pointwise cover

The conditional redraw `statePair θ st` draws two incidences independently inside one finite
state. A set `D` of pairs is bounded by a finite family of rectangles `E x y ×ˢ V y`, as soon as
every pair of `D` inside one state and inside a full-measure set `G₀` lies in one of them:

* `agree_statePair_ne_state_eq_zero`: the pairs in different states carry no mass;
* `agree_statePair_fst_null`, `agree_statePair_snd_null`: pairs whose first (second) incidence lies in a
  null set carry no mass;
* `agree_statePair_le_of_cover`: with a statewise cap `θ (V y ∩ st⁻¹{q}) ≤ c y θ (st⁻¹{q})` of the
  target sets, `statePair θ st D ≤ Σₓ Σ_y c y θ (E x y)`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The conditional redraw only draws pairs inside one state. -/
theorem agree_statePair_ne_state_eq_zero {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (θ : Measure Ω) [IsFiniteMeasure θ] (st : Ω → Q) (hs : ∀ q, MeasurableSet (st ⁻¹' {q})) :
    statePair θ st {p | st p.1 ≠ st p.2} = 0 := by
  classical
  simp only [statePair, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro q _
  have hsub : {p : Ω × Ω | st p.1 ≠ st p.2} ⊆
      ((st ⁻¹' {q})ᶜ ×ˢ univ) ∪ (univ ×ˢ (st ⁻¹' {q})ᶜ) := by
    intro p hp
    by_cases h1 : st p.1 = q
    · refine mem_union_right _ ⟨mem_univ _, ?_⟩
      intro h2
      have h2' : st p.2 = q := h2
      exact hp (h1.trans h2'.symm)
    · exact mem_union_left _ ⟨h1, mem_univ _⟩
  have hzero : ((θ.restrict (st ⁻¹' {q})).prod (θ.restrict (st ⁻¹' {q})))
      (((st ⁻¹' {q})ᶜ ×ˢ univ) ∪ (univ ×ˢ (st ⁻¹' {q})ᶜ)) = 0 := by
    apply measure_union_null
    · rw [Measure.prod_prod, Measure.restrict_apply (hs q).compl, compl_inter_self,
        measure_empty, zero_mul]
    · rw [Measure.prod_prod, Measure.restrict_apply (hs q).compl, compl_inter_self,
        measure_empty, mul_zero]
  rw [measure_mono_null hsub hzero, mul_zero]

/-- Pairs whose first incidence lies in a null set carry no mass. -/
theorem agree_statePair_fst_null {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (θ : Measure Ω) [IsFiniteMeasure θ] (st : Ω → Q) (hs : ∀ q, MeasurableSet (st ⁻¹' {q}))
    {N : Set Ω} (hN : MeasurableSet N) (hnull : θ N = 0) :
    statePair θ st (N ×ˢ univ) = 0 := by
  refine le_antisymm ?_ zero_le
  calc
    statePair θ st (N ×ˢ univ) ≤ 1 * θ N :=
      statePair_rectangle_cap θ st hs 1 N univ hN MeasurableSet.univ
        (fun q => by rw [univ_inter, one_mul])
    _ = 0 := by rw [hnull, mul_zero]

/-- Pairs whose second incidence lies in a null set carry no mass. -/
theorem agree_statePair_snd_null {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (θ : Measure Ω) [IsFiniteMeasure θ] (st : Ω → Q) (hs : ∀ q, MeasurableSet (st ⁻¹' {q}))
    {N : Set Ω} (hN : MeasurableSet N) (hnull : θ N = 0) :
    statePair θ st (univ ×ˢ N) = 0 := by
  refine le_antisymm ?_ zero_le
  calc
    statePair θ st (univ ×ˢ N) ≤ 0 * θ univ :=
      statePair_rectangle_cap θ st hs 0 univ N MeasurableSet.univ hN
        (fun q => by
          rw [zero_mul]
          exact le_of_eq (measure_mono_null inter_subset_left hnull))
    _ = 0 := zero_mul _

/-- **Pair-disagreement mass from a pointwise cover.** If every pair of `D` inside one state,
with both incidences in the full-measure set `G₀`, lies in some rectangle `E x y ×ˢ V y`
(`x ∈ S`, `y ∈ T x`), and the target sets are capped statewise by `c y`, then the conditional
redraw gives `D` mass at most `Σₓ Σ_y c y θ (E x y)`. -/
theorem agree_statePair_le_of_cover {Ω Q Src Tgt : Type*} [MeasurableSpace Ω] [Fintype Q]
    (θ : Measure Ω) [IsFiniteMeasure θ] (st : Ω → Q) (hs : ∀ q, MeasurableSet (st ⁻¹' {q}))
    (G₀ : Set Ω) (hG₀ : MeasurableSet G₀) (hnull : θ G₀ᶜ = 0)
    (D : Set (Ω × Ω)) (S : Finset Src) (T : Src → Finset Tgt)
    (E : Src → Tgt → Set Ω) (V : Tgt → Set Ω)
    (hE : ∀ x y, MeasurableSet (E x y)) (hV : ∀ y, MeasurableSet (V y))
    (c : Tgt → ℝ≥0∞) (hcap : ∀ y q, θ (V y ∩ st ⁻¹' {q}) ≤ c y * θ (st ⁻¹' {q}))
    (hcover : ∀ ω ∈ G₀, ∀ ω' ∈ G₀, st ω = st ω' → (ω, ω') ∈ D →
      ∃ x ∈ S, ∃ y ∈ T x, ω ∈ E x y ∧ ω' ∈ V y) :
    statePair θ st D ≤ ∑ x ∈ S, ∑ y ∈ T x, c y * θ (E x y) := by
  have h1 := agree_statePair_fst_null θ st hs hG₀.compl hnull
  have h2 := agree_statePair_snd_null θ st hs hG₀.compl hnull
  have h3 := agree_statePair_ne_state_eq_zero θ st hs
  have hrect : ∀ x y, statePair θ st (E x y ×ˢ V y) ≤ c y * θ (E x y) := fun x y =>
    statePair_rectangle_cap θ st hs (c y) (E x y) (V y) (hE x y) (hV y) (hcap y)
  have hsub : D ⊆ ((G₀ᶜ ×ˢ univ) ∪ (univ ×ˢ G₀ᶜ) ∪ {p | st p.1 ≠ st p.2}) ∪
      ⋃ x ∈ S, ⋃ y ∈ T x, E x y ×ˢ V y := by
    rintro ⟨ω, ω'⟩ hp
    by_cases hω : ω ∈ G₀
    · by_cases hω' : ω' ∈ G₀
      · by_cases hst : st ω = st ω'
        · obtain ⟨x, hx, y, hy, hxE, hyV⟩ := hcover ω hω ω' hω' hst hp
          refine mem_union_right _ ?_
          simp only [mem_iUnion, mem_prod]
          exact ⟨x, hx, y, hy, hxE, hyV⟩
        · exact mem_union_left _ (mem_union_right _ hst)
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _ ⟨mem_univ _, hω'⟩))
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ ⟨hω, mem_univ _⟩))
  calc
    statePair θ st D ≤ statePair θ st
        (((G₀ᶜ ×ˢ univ) ∪ (univ ×ˢ G₀ᶜ) ∪ {p | st p.1 ≠ st p.2}) ∪
          ⋃ x ∈ S, ⋃ y ∈ T x, E x y ×ˢ V y) := measure_mono hsub
    _ ≤ statePair θ st ((G₀ᶜ ×ˢ univ) ∪ (univ ×ˢ G₀ᶜ) ∪ {p | st p.1 ≠ st p.2}) +
        statePair θ st (⋃ x ∈ S, ⋃ y ∈ T x, E x y ×ˢ V y) := measure_union_le _ _
    _ = statePair θ st (⋃ x ∈ S, ⋃ y ∈ T x, E x y ×ˢ V y) := by
        rw [measure_union_null (measure_union_null h1 h2) h3, zero_add]
    _ ≤ ∑ x ∈ S, statePair θ st (⋃ y ∈ T x, E x y ×ˢ V y) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ S, ∑ y ∈ T x, statePair θ st (E x y ×ˢ V y) :=
        Finset.sum_le_sum fun x _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ S, ∑ y ∈ T x, c y * θ (E x y) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hrect x y

end

end Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels
