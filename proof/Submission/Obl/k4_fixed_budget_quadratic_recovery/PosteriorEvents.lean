/- Adapted within this LOT tree from o120/x0402, commit 70956fccdfd7e9924a3fa094355c65a03c16ee9c,
Submission/Obl/k4_unbounded_width_exclusion/PosteriorEvents.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.RealPosterior

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Finset

variable {X β : Type*} [MeasurableSpace X] [Fintype β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

theorem measurableSet_list_event (L : X → Finset β)
    (hL : ∀ b, MeasurableSet {x | b ∈ L x}) :
    MeasurableSet {p : β × X | p.1 ∈ L p.2} := by
  have heq : {p : β × X | p.1 ∈ L p.2} =
      ⋃ b, ({b} ×ˢ {x | b ∈ L x}) := by ext p; simp
  rw [heq]
  exact MeasurableSet.iUnion (fun b => (measurableSet_singleton b).prod (hL b))

theorem posteriorColorLaw_list (μ : Measure X) (π : X → β → ENNReal)
    (hπ : ∀ b, Measurable (fun x => π x b))
    (L : X → Finset β) (hL : ∀ b, MeasurableSet {x | b ∈ L x}) :
    posteriorColorLaw μ π {p | p.1 ∈ L p.2} = ∫⁻ x, ∑ b ∈ L x, π x b ∂μ := by
  classical
  have hE := measurableSet_list_event L hL
  have hmap (b : β) :
      ((μ.withDensity (fun x => π x b)).map (fun x => (b, x))) {p | p.1 ∈ L p.2} =
        ∫⁻ x, if b ∈ L x then π x b else 0 ∂μ := by
    rw [Measure.map_apply (by fun_prop) hE]
    change μ.withDensity (fun x => π x b) {x | b ∈ L x} = _
    rw [withDensity_apply _ (hL b), ← lintegral_indicator (hL b)]
    exact lintegral_congr (fun x => by simp [Set.indicator_apply])
  unfold posteriorColorLaw
  rw [Measure.finsetSum_apply]
  simp_rw [hmap]
  calc
    _ = ∫⁻ x, ∑ b, if b ∈ L x then π x b else 0 ∂μ := by
      symm
      apply lintegral_finsetSum
      intro b _
      exact (hπ b).piecewise (hL b) measurable_const
    _ = _ := lintegral_congr (fun x => by simp)

theorem posteriorColorLaw_list_real (μ : Measure X) (π : X → β → ℝ)
    (hπ : ∀ b, Measurable (fun x => π x b)) (hnonneg : ∀ x b, 0 ≤ π x b)
    (L : X → Finset β) (hL : ∀ b, MeasurableSet {x | b ∈ L x}) :
    (posteriorColorLaw μ (fun x b => ENNReal.ofReal (π x b))
      {p | p.1 ∈ L p.2}).toReal = ∫ x, ∑ b ∈ L x, π x b ∂μ := by
  classical
  rw [posteriorColorLaw_list _ _ (fun b => (hπ b).ennreal_ofReal) L hL]
  have hmeas : Measurable (fun x => ∑ b ∈ L x, ENNReal.ofReal (π x b)) := by
    have heq : (fun x => ∑ b ∈ L x, ENNReal.ofReal (π x b)) =
        fun x => ∑ b, if b ∈ L x then ENNReal.ofReal (π x b) else 0 := by
      ext x
      simp
    rw [heq]
    exact Finset.measurable_sum _
      (fun b _ => (hπ b).ennreal_ofReal.piecewise (hL b) measurable_const)
  rw [← integral_toReal hmeas.aemeasurable
    (Filter.Eventually.of_forall (fun _ => lt_top_iff_ne_top.mpr
      (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top))))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl (fun b _ => ENNReal.toReal_ofReal (hnonneg x b))

/-- Lists evaluated in the RN color law have their original observed
component masses, including components of arbitrarily small weight. -/
theorem componentPosteriorColorLaw_list (ρ : β → Measure X)
    [∀ b, IsFiniteMeasure (ρ b)] (L : X → Finset β)
    (hL : ∀ b, MeasurableSet {x | b ∈ L x}) :
    posteriorColorLaw (∑ b, ρ b) (componentPosterior ρ) {p | p.1 ∈ L p.2} =
      ∑ b, ρ b {x | b ∈ L x} := by
  unfold posteriorColorLaw
  simp_rw [componentPosterior_density]
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [Measure.map_apply (by fun_prop) (measurableSet_list_event L hL)]
  rfl

theorem componentPosteriorColorLaw_list_real (ρ : β → Measure X)
    [∀ b, IsFiniteMeasure (ρ b)] (L : X → Finset β)
    (hL : ∀ b, MeasurableSet {x | b ∈ L x}) :
    (posteriorColorLaw (∑ b, ρ b) (componentPosterior ρ)).real {p | p.1 ∈ L p.2} =
      ∑ b, (ρ b).real {x | b ∈ L x} := by
  simp only [measureReal_def, componentPosteriorColorLaw_list ρ L hL,
    ENNReal.toReal_sum (fun b _ => measure_ne_top (ρ b) _)]

/-- Pairwise agreement is exactly the posterior neighbor mass, with the
observation measure kept unnormalized. -/
theorem posteriorPairLaw_neighbors (μ : Measure X) (π : X → β → ENNReal)
    (hπ : ∀ b, Measurable (fun x => π x b)) (neighbors : β → Finset β) :
    posteriorPairLaw μ π {p | p.1.2 ∈ neighbors p.1.1} =
      ∫⁻ x, ∑ b, π x b * ∑ a ∈ neighbors b, π x a ∂μ := by
  classical
  have hE : MeasurableSet {p : (β × β) × X | p.1.2 ∈ neighbors p.1.1} := by
    have h : Measurable (fun p : β × β => decide (p.2 ∈ neighbors p.1)) :=
      measurable_of_finite _
    simpa only [Function.comp_apply, decide_eq_true_eq] using
      measurableSet_eq_fun (h.comp measurable_fst)
        (measurable_const : Measurable (fun _ : (β × β) × X => true))
  have hmap (b a : β) :
      ((μ.withDensity (fun x => π x b * π x a)).map (fun x => ((b, a), x)))
          {p | p.1.2 ∈ neighbors p.1.1} =
        if a ∈ neighbors b then ∫⁻ x, π x b * π x a ∂μ else 0 := by
    rw [Measure.map_apply (by fun_prop) hE]
    by_cases ha : a ∈ neighbors b
    · simp [Set.preimage_ofPred_eq, ha, withDensity_apply _ MeasurableSet.univ]
    · simp [Set.preimage_ofPred_eq, ha]
  unfold posteriorPairLaw
  simp only [Measure.finsetSum_apply, hmap]
  calc
    _ = ∑ b, ∫⁻ x, ∑ a ∈ neighbors b, π x b * π x a ∂μ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [lintegral_finsetSum (f := fun a x => π x b * π x a)
        (neighbors b) (fun a _ => (hπ b).mul (hπ a))]
      simp
    _ = ∫⁻ x, ∑ b, ∑ a ∈ neighbors b, π x b * π x a ∂μ := by
      symm
      apply lintegral_finsetSum
      intro b _
      exact Finset.measurable_sum _ (fun a _ => (hπ b).mul (hπ a))
    _ = _ := by simp_rw [← Finset.mul_sum]

theorem posteriorPairLaw_neighbors_real (μ : Measure X) (π : X → β → ℝ)
    (hπ : ∀ b, Measurable (fun x => π x b)) (hnonneg : ∀ x b, 0 ≤ π x b)
    (neighbors : β → Finset β) :
    (posteriorPairLaw μ (fun x b => ENNReal.ofReal (π x b))
      {p | p.1.2 ∈ neighbors p.1.1}).toReal =
      ∫ x, ∑ b, π x b * ∑ a ∈ neighbors b, π x a ∂μ := by
  rw [posteriorPairLaw_neighbors _ _ (fun b => (hπ b).ennreal_ofReal)]
  have hterm (x : X) (b : β) :
      ENNReal.ofReal (π x b) * ∑ a ∈ neighbors b, ENNReal.ofReal (π x a) ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)
  have hreal (x : X) :
      (∑ b, ENNReal.ofReal (π x b) * ∑ a ∈ neighbors b,
        ENNReal.ofReal (π x a)).toReal = ∑ b, π x b * ∑ a ∈ neighbors b, π x a := by
    rw [ENNReal.toReal_sum (fun b _ => hterm x b)]
    apply Finset.sum_congr rfl
    intro b _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hnonneg x b),
      ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => ENNReal.toReal_ofReal (hnonneg x a))
  rw [← integral_toReal (by fun_prop)
    (Filter.Eventually.of_forall (fun x => lt_top_iff_ne_top.mpr
      (ENNReal.sum_ne_top.mpr (fun b _ => hterm x b))))]
  exact integral_congr_ae (Filter.Eventually.of_forall hreal)

end Submission.Obl.k4_fixed_budget_quadratic_recovery
