import Mathlib

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set

/-- The observed law of each assigned piece, with no normalization. -/
def observedComponents {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (C : ι → Set Ω) (O : Ω → X) (i : ι) : Measure X :=
  (μ.restrict (C i)).map O

theorem observedComponents_isFinite
    {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (C : ι → Set Ω) (O : Ω → X) (i : ι) :
    IsFiniteMeasure (observedComponents μ C O i) := by
  unfold observedComponents
  infer_instance

/-- The total observed component mass equals the covered mass under the original law. -/
theorem observedComponents_total_real
    {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (C : ι → Set Ω)
    (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (O : Ω → X) (hO : Measurable O) :
    (∑ i, observedComponents μ C O i).real univ = μ.real (⋃ i, C i) := by
  have hfin (i : ι) := observedComponents_isFinite μ C O i
  have heach (i : ι) : observedComponents μ C O i univ = μ (C i) := by
    simp [observedComponents, Measure.map_apply hO MeasurableSet.univ]
  simp only [measureReal_def, Measure.finsetSum_apply, heach]
  rw [measure_iUnion hdisj hC, tsum_fintype]

/-- Lists scored under the observed components have exactly their success mass
under the original source law. -/
theorem observedComponents_success_real
    {Ω X ι β : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Fintype ι]
    [DecidableEq β]
    (μ : Measure Ω) [IsFiniteMeasure μ] (C : ι → Set Ω)
    (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (O : Ω → X) (hO : Measurable O)
    (code : ι → β) (L : X → Finset β)
    (hL : ∀ b, MeasurableSet {x | b ∈ L x}) :
    (∑ i, (observedComponents μ C O i).real {x | code i ∈ L x}) =
      μ.real {p | ∃ i, p ∈ C i ∧ code i ∈ L (O p)} := by
  let D : ι → Set Ω := fun i => C i ∩ O ⁻¹' {x | code i ∈ L x}
  have hD : ∀ i, MeasurableSet (D i) := fun i => (hC i).inter ((hL (code i)).preimage hO)
  have hDdisj : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    exact (hdisj hij).mono inter_subset_left inter_subset_left
  have hEq : {p | ∃ i, p ∈ C i ∧ code i ∈ L (O p)} = ⋃ i, D i := by ext p; simp [D]
  have heach (i : ι) : (observedComponents μ C O i).real {x | code i ∈ L x} =
      μ.real (D i) := by
    simp only [measureReal_def, observedComponents, Measure.map_apply hO (hL (code i)),
      Measure.restrict_apply ((hL (code i)).preimage hO)]
    rw [inter_comm]
  simp_rw [heach]
  rw [hEq]
  exact (measureReal_iUnion_fintype hDdisj hD).symm

/-- Almost-everywhere sample properties pass to the original observed components. -/
theorem observedComponents_ae
    {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (C : ι → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (O : Ω → X) (hO : Measurable O) (Good : ι → X → Prop)
    (hGood : ∀ i, MeasurableSet {x | Good i x})
    (hsample : ∀ i, ∀ᵐ p ∂μ, p ∈ C i → Good i (O p)) (i : ι) :
    ∀ᵐ x ∂observedComponents μ C O i, Good i x := by
  rw [observedComponents, ae_map_iff hO.aemeasurable (hGood i), ae_restrict_iff' (hC i)]
  exact hsample i

end Submission.Obl.k4_fixed_budget_quadratic_recovery
