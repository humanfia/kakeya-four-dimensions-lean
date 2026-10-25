import Submission.Obl.k4_fixed_prior_chart_regularization.Defs
import Submission.Obl.k4_fixed_prior_chart_regularization.Regularization

namespace Submission.Obl.k4_fixed_prior_chart_regularization

open MeasureTheory Set

/-- The frozen statement written using the conjunction interfaces. -/
def Statement : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
      ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ),
        Input ν y β γ E F (N ^ (-c)) d (N ^ η) →
        ∃ E' : Set (Ω × ℝ), E' ⊆ E ∧ Output ν y β γ E' F (N ^ (-c)) d (N ^ ε)

/-- Converting the frozen input conjunction adds no assumptions. -/
theorem raw_of_input {Ω : Type} [MeasurableSpace Ω]
    {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {ζ d K : ℝ} (h : Input ν y β γ E F ζ d K) :
    UnregularizedChart ν y β γ E F d K ζ := by
  obtain ⟨hy, hβ, hγ, hF, hE, hunit, hby, hbβ, hbγ, hbF, hmass, hcap, hsupp⟩ := h
  exact ⟨hy, hβ, hγ, hF, hE, hunit, hby, hbβ, hbγ, hbF, hmass, hcap, hsupp⟩

/-- All final fields refer to the unchanged original prior and functions. -/
theorem output_of_data {Ω : Type} [MeasurableSpace Ω]
    {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {ζ d K : ℝ} (h : FirstJet.Data ν y β γ E F d K ζ) :
    Output ν y β γ E F ζ d K := by
  exact ⟨h.measurable_y, h.measurable_β, h.measurable_γ, h.measurable_F,
    h.measurableSet_E, h.subset_E, h.bound_y, h.bound_β, h.bound_γ, h.bound_F,
    h.mass, h.support, h.absCap, h.rowLip, h.slopeLip, h.binCap⟩

/-- The structural chart statement is exactly the frozen obligation. -/
theorem statement_of_chartRegularization (h : ChartRegularization) : Statement := by
  intro d hd hd1 c hc ε hε
  obtain ⟨η, hη, hηε, N₀, hN₀, hreg⟩ := h d hd hd1 c hc ε hε
  refine ⟨η, hη, hηε, N₀, hN₀, ?_⟩
  intro N hN Ω mΩ ν hν y β γ E F hinput
  obtain ⟨E', hsub, hdata⟩ := hreg N hN Ω ν hν y β γ E F (raw_of_input hinput)
  exact ⟨E', hsub, output_of_data hdata⟩

end Submission.Obl.k4_fixed_prior_chart_regularization
