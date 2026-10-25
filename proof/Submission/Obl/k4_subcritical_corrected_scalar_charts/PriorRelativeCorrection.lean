/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/PriorRelativeCorrection.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.DirectionalCorrection
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Conditioning

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

noncomputable section

/-- Apply time-polynomial selection relative to the full original chart prior,
then restore its unchanged original incidence law. The returned floor has the
original prior factor; no lower bound on an individual chart prior is needed. -/
theorem exists_prior_relative_directional_correction {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    (A : Set α) (hA₀ : ν A ≠ 0)
    (Hb : α → Fin 6 → ℝ) (H0 : Fin 6 → ℝ) (r : ℝ) (signal : ℝ → ℝ)
    (hsignal_meas : Measurable signal)
    {K m S δ : ℝ} (hK : 0 < K) (hm : 0 < m) (hmK : m ≤ K)
    (hS : 0 ≤ S) (hδ : 0 ≤ δ)
    (hdom : ρ ≤ ENNReal.ofReal K • (ν.prod volume))
    {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (hfloor : ENNReal.ofReal m * ν A ≤ ρ E)
    (hsub : E ⊆ A ×ˢ Icc (0 : ℝ) 1)
    (hsignal : ∀ p ∈ E, |signal p.2| ≤ S)
    (hfit : ∀ p ∈ E,
      |r * fiberDerivative (Hb p.1 - H0) p.2 - signal p.2| ≤ δ) :
    ∃ β : Fin 3 → ℝ,
      (∀ i, |β i| ≤ 17 * (96 * K / m) ^ 2 * (S + δ)) ∧
      ENNReal.ofReal ((ν A).toReal * (m ^ 2 / (8 * K))) ≤
        ρ {p | p ∈ E ∧ |signal p.2 - fiberDerivative (fiberCorrection β) p.2| ≤ δ} := by
  let σ := conditionedIncidences ν ρ A
  letI : IsProbabilityMeasure (ProbabilityTheory.cond ν A) :=
    ProbabilityTheory.cond_isProbabilityMeasure hA₀
  have hdom' : σ ≤ ENNReal.ofReal K • ((ProbabilityTheory.cond ν A).prod volume) :=
    conditionedIncidences_domination ν ρ A _ hdom
  have hEA : E ∩ (A ×ˢ (univ : Set ℝ)) = E :=
    inter_eq_left.mpr (hsub.trans (Set.prod_mono subset_rfl (subset_univ _)))
  have hmass : ENNReal.ofReal m ≤ σ E := by
    dsimp [σ, conditionedIncidences]
    rw [Measure.restrict_apply hE, hEA]
    calc
      _ = (ν A)⁻¹ * (ENNReal.ofReal m * ν A) := by
        rw [mul_left_comm, ENNReal.inv_mul_cancel hA₀ (measure_ne_top ν A), mul_one]
      _ ≤ _ := mul_le_mul_right hfloor _
  obtain ⟨β, hβ, hret⟩ := exists_directional_correction_of_mass
    (ProbabilityTheory.cond ν A) σ Hb H0 r signal hK hm hmK hS hδ hdom' hE hmass
    (hsub.trans (Set.prod_mono (subset_univ _) subset_rfl)) hsignal hfit
  refine ⟨β, hβ, ?_⟩
  have hfiber : Measurable (fun p : α × ℝ => fiberDerivative (fiberCorrection β) p.2) := by
    unfold fiberDerivative
    fun_prop
  have hT : MeasurableSet {p : α × ℝ | p ∈ E ∧
      |signal p.2 - fiberDerivative (fiberCorrection β) p.2| ≤ δ} :=
    hE.inter (measurableSet_le ((hsignal_meas.comp measurable_snd).sub hfiber).abs measurable_const)
  have hh := conditionedIncidences_floor_return ν ρ A hA₀ (measure_ne_top ν A) _ hT
    (show 0 ≤ m ^ 2 / (8 * K) by positivity) hret
  rw [inter_eq_left.mpr (show {p : α × ℝ | p ∈ E ∧
      |signal p.2 - fiberDerivative (fiberCorrection β) p.2| ≤ δ} ⊆ A ×ˢ univ from
    fun p hp => ⟨(hsub hp.1).1, mem_univ _⟩)] at hh
  exact hh

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
