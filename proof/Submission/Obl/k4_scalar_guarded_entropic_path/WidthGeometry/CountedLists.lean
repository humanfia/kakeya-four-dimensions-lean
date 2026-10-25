/-
Adapted from this LOT tree, obligation o134, session x0438, commit 2e990309978b,
Submission/Obl/k4_scalar_guarded_tangent_obstruction/CountedLists.lean.
Its original attribution comments are retained below.
-/
import Mathlib

namespace Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry

open MeasureTheory Set

variable {X β : Type*} [MeasurableSpace X] [MeasurableSpace β]
  [Countable β] [MeasurableSingletonClass β]

def countedListEvent (L : X → Finset β) : Set (X × β) :=
  {z | z.2 ∈ L z.1}

theorem measurableSet_countedListEvent (L : X → Finset β)
    (hL : ∀ b, MeasurableSet {x | b ∈ L x}) : MeasurableSet (countedListEvent L) := by
  have heq : countedListEvent L = ⋃ b : β, {x | b ∈ L x} ×ˢ {b} := by
    ext z
    simp only [countedListEvent, mem_ofPred_eq, mem_iUnion, mem_prod, mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨z.2, hz, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact hb
  rw [heq]
  exact MeasurableSet.iUnion (fun b => (hL b).prod (measurableSet_singleton b))

/-- Counting labels over a fixed base costs the list cardinality, even
when the ambient label type is merely countable. -/
theorem measure_countedListEvent_le (σ : Measure X) [SFinite σ]
    (L : X → Finset β) (hL : ∀ b, MeasurableSet {x | b ∈ L x})
    (D : ENNReal) (hcard : ∀ x, (L x).card ≤ D) :
    (σ.prod Measure.count) (countedListEvent L) ≤ D * σ Set.univ := by
  rw [Measure.prod_apply (measurableSet_countedListEvent L hL)]
  have hsection (x : X) : Measure.count (Prod.mk x ⁻¹' countedListEvent L) =
      ((L x).card : ENNReal) := by
    change Measure.count (L x : Set β) = _
    exact Measure.count_apply_finset _
  simp_rw [hsection]
  exact (lintegral_mono (fun x => hcard x)).trans_eq (by simp)

/-- A joint ceiling and a finite list at the original observation give
an original-law mass bound, with no conditioning on successful labels. -/
theorem mass_le_counted_list_budget (σ : Measure X) [SFinite σ]
    (ξ : Measure (X × β)) (L : X → Finset β)
    (hL : ∀ b, MeasurableSet {x | b ∈ L x}) (c D : ENNReal)
    (hcard : ∀ x, (L x).card ≤ D)
    (hdom : ξ ≤ c • (σ.prod Measure.count))
    (hsupport : ξ (countedListEvent L)ᶜ = 0) :
    ξ Set.univ ≤ (c * D) * σ Set.univ := by
  have hmass : ξ Set.univ ≤ ξ (countedListEvent L) := by
    calc
      ξ Set.univ = ξ (countedListEvent L ∪ (countedListEvent L)ᶜ) := by
        rw [union_compl_self]
      _ ≤ ξ (countedListEvent L) + ξ (countedListEvent L)ᶜ := measure_union_le _ _
      _ = ξ (countedListEvent L) := by rw [hsupport, add_zero]
  calc
    ξ Set.univ ≤ ξ (countedListEvent L) := hmass
    _ ≤ (c • (σ.prod Measure.count)) (countedListEvent L) := hdom _
    _ = c * (σ.prod Measure.count) (countedListEvent L) := by
      rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ c * (D * σ Set.univ) := by
      gcongr
      exact measure_countedListEvent_le σ L hL D hcard
    _ = (c * D) * σ Set.univ := by rw [mul_assoc]

/-- The counted-list bound pulled back to the original incidence space.
The reference observation marginal is always taken from `μ₀`. -/
theorem original_mass_le_list_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ₀ μ : Measure Ω) [IsFiniteMeasure μ₀]
    (observe : Ω → X) (bin : Ω → β) (hobserve : Measurable observe) (hbin : Measurable bin)
    (L : X → Finset β) (hL : ∀ b, MeasurableSet {x | b ∈ L x}) (c D : ENNReal)
    (hcard : ∀ x, (L x).card ≤ D)
    (hdom : μ.map (fun ω => (observe ω, bin ω)) ≤ c • ((μ₀.map observe).prod Measure.count))
    (hcover : ∀ᵐ ω ∂μ, bin ω ∈ L (observe ω)) :
    μ Set.univ ≤ (c * D) * μ₀ Set.univ := by
  have hmap : Measurable (fun ω => (observe ω, bin ω)) := hobserve.prodMk hbin
  have hsupport : (μ.map (fun ω => (observe ω, bin ω))) (countedListEvent L)ᶜ = 0 := by
    rw [Measure.map_apply hmap (measurableSet_countedListEvent L hL).compl]
    exact ae_iff.mp hcover
  have hbound := mass_le_counted_list_budget (μ₀.map observe)
    (μ.map (fun ω => (observe ω, bin ω))) L hL c D hcard hdom hsupport
  simpa only [Measure.map_apply hmap MeasurableSet.univ,
    Measure.map_apply hobserve MeasurableSet.univ, preimage_univ] using hbound

end Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry
