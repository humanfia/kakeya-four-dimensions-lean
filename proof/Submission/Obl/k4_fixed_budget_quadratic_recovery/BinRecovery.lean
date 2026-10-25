import Submission.Obl.k4_fixed_budget_quadratic_recovery.BinLists
import Submission.Obl.k4_fixed_budget_quadratic_recovery.PosteriorEvents
import Submission.Obl.k4_fixed_budget_quadratic_recovery.CoefficientBins

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Finset Set

variable {X β : Type*} [MeasurableSpace X] [Fintype β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Integrating the finite maximizing rule retains the unnormalized posterior
neighbor mass, even when many component indices have the same coefficient bin. -/
theorem recover_bin_neighbor_events
    (μ : Measure X) [IsFiniteMeasure μ]
    (π : X → β → ℝ) (hπ : ∀ a, Measurable (fun x => π x a))
    (hnonneg : ∀ x a, 0 ≤ π x a) (hmass : ∀ x, ∑ a, π x a ≤ 1)
    (code : β → Fin 6 → ℤ) :
    ∃ L : X → Finset (Fin 6 → ℤ),
      (∀ q, MeasurableSet {x | q ∈ L x}) ∧ (∀ x, (L x).card ≤ 3 ^ 6) ∧
      (posteriorPairLaw μ (fun x b => ENNReal.ofReal (π x b))).real
          {p | p.1.2 ∈ binNeighborIndices code p.1.1} ≤
      (posteriorColorLaw μ (fun x b => ENNReal.ofReal (π x b))).real
          {p | code p.1 ∈ L p.2} := by
  classical
  obtain ⟨L, hLm, hLcard, hpoint⟩ := exists_measurable_bin_lists π hπ hnonneg hmass code
  let L' : X → Finset β := fun x => Finset.univ.filter (fun a => code a ∈ L x)
  have hL'm (a : β) : MeasurableSet {x | a ∈ L' x} := by
    simpa only [L', Finset.mem_filter, Finset.mem_univ, true_and] using hLm (code a)
  have hπint (a : β) : Integrable (fun x => π x a) μ := by
    apply Integrable.of_bound (hπ a).aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x a)]
    exact (Finset.single_le_sum (fun b _ => hnonneg x b) (Finset.mem_univ a)).trans (hmass x)
  have hLint : Integrable (fun x => ∑ a ∈ L' x, π x a) μ :=
    Submission.Lib.K4OriginalLists.integrable_listDensity μ π L' hπint hL'm
  have hpairint : Integrable
      (fun x => ∑ b, π x b * ∑ a ∈ binNeighborIndices code b, π x a) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with x
    have hnn : 0 ≤ ∑ b, π x b * ∑ a ∈ binNeighborIndices code b, π x a :=
      Finset.sum_nonneg (fun b _ => mul_nonneg (hnonneg x b)
        (Finset.sum_nonneg (fun a _ => hnonneg x a)))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact (hpoint x).trans ((Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (L' x)) (fun a _ _ => hnonneg x a)).trans (hmass x))
  have hevent : {p : β × X | code p.1 ∈ L p.2} =
      {p | p.1 ∈ L' p.2} := by
    ext p
    simp [L']
  refine ⟨L, hLm, hLcard, ?_⟩
  rw [hevent]
  simp only [measureReal_def, posteriorPairLaw_neighbors_real μ π hπ hnonneg,
    posteriorColorLaw_list_real μ π hπ hnonneg L' hL'm]
  exact integral_mono hpairint hLint hpoint

/-- Bin-list recovery for finite observed component measures.  The density
reference and the recovered success both keep the original total mass. -/
theorem recover_component_bin_lists
    (ρ : β → Measure X) [∀ i, IsFiniteMeasure (ρ i)]
    (c : β → Fin 6 → ℝ) {h e : ℝ} (hh : 0 < h) (he : 0 ≤ e)
    (hbad : (posteriorPairLaw (∑ i, ρ i) (componentPosterior ρ))
      {p | ∃ a : Fin 6, h < |c p.1.1 a - c p.1.2 a|} ≤ ENNReal.ofReal e) :
    ∃ L : X → Finset (Fin 6 → ℤ),
      (∀ q, MeasurableSet {x | q ∈ L x}) ∧ (∀ x, (L x).card ≤ 3 ^ 6) ∧
      (∑ i, (ρ i).real Set.univ) - e ≤
        ∑ i, (ρ i).real {x | coefficientBin h (c i) ∈ L x} := by
  classical
  let code : β → Fin 6 → ℤ := fun i => coefficientBin h (c i)
  let τ := posteriorPairLaw (∑ i, ρ i) (componentPosterior ρ)
  have hτtotal : τ univ = ∑ i, ρ i univ := componentPosteriorPair_total_mass ρ
  letI : IsFiniteMeasure τ := ⟨by
    rw [hτtotal]
    exact ENNReal.sum_lt_top.mpr (fun i _ => measure_lt_top (ρ i) univ)⟩
  let E : Set ((β × β) × X) := {p | p.1.2 ∈ binNeighborIndices code p.1.1}
  have hEm : MeasurableSet E := by
    exact (Set.toFinite {q : β × β | q.2 ∈ binNeighborIndices code q.1}).measurableSet.preimage
      measurable_fst
  have hsub : Eᶜ ⊆ {p | ∃ a : Fin 6, h < |c p.1.1 a - c p.1.2 a|} := by
    intro p hp
    by_contra hn
    have hclose : ∀ a, |c p.1.2 a - c p.1.1 a| ≤ h := by
      intro a
      rw [abs_sub_comm]
      exact le_of_not_gt (fun ha => hn ⟨a, ha⟩)
    have hcodes := floor_codes_mem_binCube hh hclose
    apply hp
    change p.1.2 ∈ binNeighborIndices code p.1.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcodes⟩
  have hbadreal : τ.real {p | ∃ a : Fin 6, h < |c p.1.1 a - c p.1.2 a|} ≤ e := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
    simpa only [measureReal_def, ENNReal.toReal_ofReal he] using h
  have hsmall : τ.real Eᶜ ≤ e := (measureReal_mono hsub).trans hbadreal
  have hmass : (∑ i, (ρ i).real univ) - e ≤ τ.real E := by
    have hreal : τ.real univ = ∑ i, (ρ i).real univ := by
      simp only [measureReal_def, hτtotal,
        ENNReal.toReal_sum (fun i _ => measure_ne_top (ρ i) univ)]
    rw [measureReal_compl hEm, hreal] at hsmall
    linarith
  obtain ⟨L, hLm, hLcard, hsuccess⟩ := recover_bin_neighbor_events (∑ i, ρ i)
    (realPosterior (componentPosterior ρ))
    (realPosterior_measurable _ (componentPosterior_measurable ρ))
    (realPosterior_nonneg _) (realPosterior_mass_le _) code
  refine ⟨L, hLm, hLcard, hmass.trans ?_⟩
  have hL'm (i : β) : MeasurableSet {x | code i ∈ L x} := hLm (code i)
  rw [realPosterior_pairLaw _ _ (componentPosterior_mass ρ),
    realPosterior_colorLaw _ _ (componentPosterior_mass ρ)] at hsuccess
  have hevent : (posteriorColorLaw (∑ i, ρ i) (componentPosterior ρ)).real
      {p | code p.1 ∈ L p.2} = ∑ i, (ρ i).real {x | code i ∈ L x} := by
    let L' : X → Finset β := fun x => Finset.univ.filter (fun i => code i ∈ L x)
    have hL' : ∀ i, MeasurableSet {x | i ∈ L' x} := fun i => by
      simpa only [L', Finset.mem_filter, Finset.mem_univ, true_and] using hL'm i
    simpa only [L', Finset.mem_filter, Finset.mem_univ, true_and] using
      componentPosteriorColorLaw_list_real ρ L' hL'
  rw [hevent] at hsuccess
  exact hsuccess

end Submission.Obl.k4_fixed_budget_quadratic_recovery
