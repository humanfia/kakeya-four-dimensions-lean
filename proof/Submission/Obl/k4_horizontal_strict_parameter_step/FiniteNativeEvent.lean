import Submission.Obl.k4_horizontal_strict_parameter_step.FiniteWidthGrid
import Submission.Obl.k4_horizontal_strict_parameter_step.IndexedJitter
import Submission.Obl.k4_horizontal_strict_parameter_step.InheritedWitnesses

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

namespace NativeModel

/-- All levels in a finite, sample-dependent depth grid share one measurable
original event with pointwise coverage and unique closed time blocks. -/
theorem finite_assignment_regular_event {α : Type} [MeasurableSpace α]
    (cfg : NativeModel α) {k : ℕ} (hν : IsProbabilityMeasure (cfg.ν k))
    (hdom : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    {J : ℕ} (s : Fin J → ℝ) (a : ∀ j, cfg.AssignmentLevel k (s j)) :
    ∃ G : Set (α × ℝ), MeasurableSet G ∧ (∀ᵐ p ∂cfg.μ k, p ∈ G) ∧
      ∀ p ∈ G, ∀ r : Fin J,
        (∃ i, p.1 ∈ cfg.B k (s r) i ∧
          p.2 ∈ Data.I (cfg.T k (s r)) (cfg.j k (s r) i)) ∧
        ∀ j j' : Fin (2 ^ cfg.T k (s r)),
          p.2 ∈ Data.I (cfg.T k (s r)) j → p.2 ∈ Data.I (cfg.T k (s r)) j' → j = j' := by
  letI := hν
  obtain ⟨G₀, hG₀, hG₀ae, hcov⟩ := cfg.finite_assignment_cover s a
  let Q : Set (α × ℝ) := {p | ∀ r : Fin J, ∀ j j' : Fin (2 ^ cfg.T k (s r)),
    p.2 ∈ Data.I (cfg.T k (s r)) j → p.2 ∈ Data.I (cfg.T k (s r)) j' → j = j'}
  have hQae : ∀ᵐ p ∂cfg.μ k, p ∈ Q := ae_all_iff.mpr fun r =>
    ae_unique_dyadic_block (cfg.ν k) (cfg.μ k) (ENNReal.ofReal (cfg.K k)) hdom (cfg.T k (s r))
  have hQnm : NullMeasurableSet Q (cfg.μ k) :=
    NullMeasurableSet.of_compl (NullMeasurableSet.of_null (ae_iff.mp hQae))
  obtain ⟨U, hUQ, hU, hUeq⟩ := hQnm.exists_measurable_subset_ae_eq
  have hUae : ∀ᵐ p ∂cfg.μ k, p ∈ U := by
    filter_upwards [hQae, hUeq] with p hp hu
    exact hu.mpr hp
  refine ⟨G₀ ∩ U, hG₀.inter hU, hG₀ae.and hUae, ?_⟩
  intro p hp r
  exact ⟨hcov p hp.1 r, hUQ hp.2 r⟩

end NativeModel

end Submission.Obl.k4_horizontal_strict_parameter_step
