import Submission.Lib.K4ListedExceptions.MeasureBounds

/-!
Original observation-law caps and finite hidden-bin support give base marginal
ceilings. The cap calculation generalizes the elementary withDensity argument
in this tree's o156/x0524 BandBounds.lean; no band-center or root selection is
needed for the abstract support projection.
-/

namespace Submission.Lib.K4ListedExceptions

open Set MeasureTheory
open scoped ENNReal

/-- Capping an observation density gives domination by the same original
reference law, without renormalizing the source measure. -/
theorem map_restrict_observation_cap_le {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (μ : Measure Ω) (ν : Measure X)
    (obs : Ω → X) (hobs : Measurable obs) (g : X → ℝ≥0∞) (hg : Measurable g)
    (hmap : μ.map obs = ν.withDensity g) (C : ℝ≥0∞) :
    (μ.restrict {ω | g (obs ω) ≤ C}).map obs ≤ C • ν := by
  apply Measure.le_iff.mpr
  intro U hU
  have hgood : MeasurableSet {x | g x ≤ C} := measurableSet_le hg measurable_const
  have hUg : MeasurableSet (U ∩ {x | g x ≤ C}) := hU.inter hgood
  rw [Measure.map_apply hobs hU, Measure.restrict_apply (hU.preimage hobs),
    Measure.smul_apply, smul_eq_mul]
  have heq : obs ⁻¹' U ∩ {ω | g (obs ω) ≤ C} = obs ⁻¹' (U ∩ {x | g x ≤ C}) := by
    ext ω
    rfl
  rw [heq, ← Measure.map_apply hobs hUg, hmap, withDensity_apply _ hUg]
  calc
    (∫⁻ x in U ∩ {x | g x ≤ C}, g x ∂ν) ≤ ∫⁻ _x in U ∩ {x | g x ≤ C}, C ∂ν := by
      apply setLIntegral_mono measurable_const
      intro x hx
      exact hx.2
    _ = C * ν (U ∩ {x | g x ≤ C}) := by rw [setLIntegral_const]
    _ ≤ C * ν U := by gcongr; exact inter_subset_left

/-- A bounded product density supported on fibers of measure at most K has a
first marginal bounded by C*K times the base law. -/
theorem supported_product_first_marginal_bound {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure (X × Y)) (μ : Measure X) (π : Measure Y) [SFinite π]
    (S : Set (X × Y)) (hS : MeasurableSet S) (hsupport : ρ Sᶜ = 0)
    {C K : ℝ≥0∞} (hdom : ρ ≤ C • μ.prod π)
    (hfiber : ∀ x, π (Prod.mk x ⁻¹' S) ≤ K)
    (U : Set X) (hU : MeasurableSet U) :
    ρ (Prod.fst ⁻¹' U) ≤ (C*K) * μ U := by
  let E : Set (X × Y) := S ∩ (Prod.fst ⁻¹' U)
  have hE : MeasurableSet E := hS.inter (hU.preimage measurable_fst)
  have hsub : E ⊆ U ×ˢ (univ : Set Y) := fun _ hp => ⟨hp.2, mem_univ _⟩
  have hvol : (μ.prod π) E ≤ K * μ U := by
    have h := prod_measure_le_of_bad_fibers μ π U ∅ univ E hU MeasurableSet.empty hE hsub
      (fun x _ _ => (measure_mono (fun _ hy => hy.1)).trans (hfiber x))
    simpa only [measure_empty, mul_zero, zero_add] using h
  have hcover : Prod.fst ⁻¹' U ⊆ E ∪ Sᶜ := by
    intro p hp
    by_cases hs : p ∈ S
    · exact Or.inl ⟨hs, hp⟩
    · exact Or.inr hs
  calc
    ρ (Prod.fst ⁻¹' U) ≤ ρ E + ρ Sᶜ := (measure_mono hcover).trans (measure_union_le _ _)
    _ = ρ E := by rw [hsupport, add_zero]
    _ ≤ (C • μ.prod π) E := Measure.le_iff.mp hdom E hE
    _ = C * (μ.prod π) E := by rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ C * (K * μ U) := mul_le_mul le_rfl hvol zero_le zero_le
    _ = (C*K) * μ U := (mul_assoc _ _ _).symm

/-- Apply the supported-product bound directly to an original observation map.
For a discrete hidden-bin law use pi=Measure.count and a finite-fiber count. -/
theorem observation_base_marginal_bound {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Ω) (μ : Measure X) (π : Measure Y) [SFinite π]
    (obs : Ω → X × Y) (hobs : Measurable obs)
    (S : Set (X × Y)) (hS : MeasurableSet S) (hsupport : ν (obs ⁻¹' Sᶜ) = 0)
    {C K : ℝ≥0∞} (hdom : ν.map obs ≤ C • μ.prod π)
    (hfiber : ∀ x, π (Prod.mk x ⁻¹' S) ≤ K)
    (U : Set X) (hU : MeasurableSet U) :
    ν {ω | (obs ω).1 ∈ U} ≤ (C*K) * μ U := by
  have hs : ν.map obs Sᶜ = 0 := by
    rw [Measure.map_apply hobs hS.compl]
    exact hsupport
  have h := supported_product_first_marginal_bound (ν.map obs) μ π S hS hs hdom hfiber U hU
  rw [Measure.map_apply hobs (hU.preimage measurable_fst)] at h
  exact h

end Submission.Lib.K4ListedExceptions
