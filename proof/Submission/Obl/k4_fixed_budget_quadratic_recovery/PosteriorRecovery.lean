/- Adapted within this LOT tree from o120/x0402, commit 70956fccdfd7e9924a3fa094355c65a03c16ee9c,
Submission/Obl/k4_unbounded_width_exclusion/PosteriorRecovery.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.PosteriorEvents
import Submission.Obl.k4_fixed_budget_quadratic_recovery.CoefficientBins

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Finset

variable {X β : Type*} [MeasurableSpace X] [Fintype β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Posterior coefficient agreement yields actual measurable lists with
at least the same success mass under the original color-observation law. -/
theorem recover_coefficient_neighbor_events
    (μ : Measure X) [IsFiniteMeasure μ]
    (π : X → β → ℝ) (hπ : ∀ a, Measurable (fun x => π x a))
    (hnonneg : ∀ x a, 0 ≤ π x a) (hmass : ∀ x, ∑ a, π x a ≤ 1)
    (code : β → Fin 6 → ℤ) (hcode : Function.Injective code) :
    ∃ L : X → Finset β, Submission.Lib.K4OriginalLists.MeasurableLists L ∧
      (∀ x, (L x).card ≤ 15 ^ 6) ∧
      (posteriorPairLaw μ (fun x b => ENNReal.ofReal (π x b))).real
        {p | p.1.2 ∈ coefficientNeighbors code p.1.1} ≤
      (posteriorColorLaw μ (fun x b => ENNReal.ofReal (π x b))).real
        {p | p.1 ∈ L p.2} := by
  obtain ⟨L, hL, hcard, hsuccess⟩ := recover_coefficient_neighbor_mass μ π hπ hnonneg hmass
    code hcode _ (posteriorPairLaw_neighbors_real μ π hπ hnonneg
      (coefficientNeighbors code)).le
  refine ⟨L, hL, hcard, ?_⟩
  simpa only [measureReal_def, posteriorColorLaw_list_real μ π hπ hnonneg L hL] using hsuccess

/-- The preceding statement applies to any finite family of observed
component measures, with no division by the total covered mass. -/
theorem recover_component_coefficient_neighbors
    (ρ : β → Measure X) [∀ b, IsFiniteMeasure (ρ b)]
    (code : β → Fin 6 → ℤ) (hcode : Function.Injective code) :
    ∃ L : X → Finset β, Submission.Lib.K4OriginalLists.MeasurableLists L ∧
      (∀ x, (L x).card ≤ 15 ^ 6) ∧
      (posteriorPairLaw (∑ b, ρ b) (componentPosterior ρ)).real
        {p | p.1.2 ∈ coefficientNeighbors code p.1.1} ≤
      ∑ b, (ρ b).real {x | b ∈ L x} := by
  obtain ⟨L, hL, hcard, hsuccess⟩ := recover_coefficient_neighbor_events (∑ b, ρ b)
    (realPosterior (componentPosterior ρ))
    (realPosterior_measurable _ (componentPosterior_measurable ρ))
    (realPosterior_nonneg _) (realPosterior_mass_le _) code hcode
  refine ⟨L, hL, hcard, ?_⟩
  simpa only [realPosterior_pairLaw _ _ (componentPosterior_mass ρ),
    realPosterior_colorLaw _ _ (componentPosterior_mass ρ),
    componentPosteriorColorLaw_list_real ρ L hL] using hsuccess

end Submission.Obl.k4_fixed_budget_quadratic_recovery
