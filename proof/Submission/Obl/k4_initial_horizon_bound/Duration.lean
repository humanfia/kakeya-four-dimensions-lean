import Mathlib

/-! Keep the original trajectory prior when pruning short labeled durations. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_initial_horizon_bound

variable {α : Type*} [MeasurableSpace α]

noncomputable def incidenceDuration (E : Set (α × ℝ)) (x : α) : ℝ≥0∞ :=
  volume (Prod.mk x ⁻¹' E)

theorem measurable_incidenceDuration {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    Measurable (incidenceDuration E) := measurable_measure_prodMk_left hE

theorem incidenceDuration_le_one {E : Set (α × ℝ)}
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (x : α) : incidenceDuration E x ≤ 1 := by
  calc
    _ ≤ volume (Icc (0 : ℝ) 1) := measure_mono (fun _ ht => (hunit ht).2)
    _ = 1 := by simp

theorem finite_duration_law (ν : Measure α) [IsFiniteMeasure ν] {E : Set (α × ℝ)}
    (hE : MeasurableSet E) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    IsFiniteMeasure (ν.withDensity (incidenceDuration E)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ _x : α, (1 : ℝ≥0∞) ∂ν := lintegral_mono (incidenceDuration_le_one hunit)
    _ < ⊤ := by simpa using measure_lt_top ν univ

/-- Integrating labeled duration against the unchanged prior gives exactly
the original incidence mass on the selected trajectory set. -/
theorem duration_integral_eq_incidence (ν : Measure α) [SFinite ν]
    {E : Set (α × ℝ)} (hE : MeasurableSet E)
    {S : Set α} (hS : MeasurableSet S) :
    (∫⁻ x in S, incidenceDuration E x ∂ν) =
      (ν.prod volume) (E ∩ (S ×ˢ univ)) := by
  rw [← Measure.restrict_apply hE, ← Measure.prod_restrict,
    Measure.restrict_univ, Measure.prod_apply hE]
  rfl

theorem duration_withDensity_apply (ν : Measure α) [SFinite ν]
    {E : Set (α × ℝ)} (hE : MeasurableSet E)
    {S : Set α} (hS : MeasurableSet S) :
    (ν.withDensity (incidenceDuration E)) S =
      (ν.prod volume) (E ∩ (S ×ˢ univ)) := by
  rw [withDensity_apply _ hS]
  exact duration_integral_eq_incidence ν hE hS

/-- Deleting entries with duration below a fixed threshold costs at most
that threshold times the total original trajectory-prior mass. -/
theorem short_duration_mass_le (ν : Measure α) {E : Set (α × ℝ)}
    (hE : MeasurableSet E) (a : ℝ≥0∞) :
    (ν.withDensity (incidenceDuration E)) {x | incidenceDuration E x < a} ≤ a * ν univ := by
  have hS : MeasurableSet {x | incidenceDuration E x < a} :=
    measurableSet_lt (measurable_incidenceDuration hE) measurable_const
  calc
    _ = ∫⁻ x in {x | incidenceDuration E x < a}, incidenceDuration E x ∂ν :=
      withDensity_apply _ hS
    _ ≤ ∫⁻ _x in {x | incidenceDuration E x < a}, a ∂ν := by
      apply setLIntegral_mono' hS
      intro x hx
      exact le_of_lt hx
    _ = a * ν {x | incidenceDuration E x < a} := by simp only [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ a * ν univ := mul_le_mul (le_refl a) (measure_mono (subset_univ _)) zero_le zero_le

/-- A duration floor converts an incidence cap into a cap for the retained
part of the original prior. No posterior or normalized replacement is used. -/
theorem retained_duration_prior_bound (ν : Measure α) {E : Set (α × ℝ)}
    (hE : MeasurableSet E) {S H : Set α} (hS : MeasurableSet S) (hH : MeasurableSet H) (a : ℝ≥0∞)
    (hfloor : ∀ x ∈ S ∩ H, a ≤ incidenceDuration E x) :
    a * (ν.restrict H) S ≤ (ν.withDensity (incidenceDuration E)) S := by
  rw [Measure.restrict_apply hS, withDensity_apply _ hS]
  calc
    a * ν (S ∩ H) = ∫⁻ _x in S ∩ H, a ∂ν := by simp only [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ x in S ∩ H, incidenceDuration E x ∂ν := by
      exact setLIntegral_mono' (hS.inter hH) hfloor
    _ ≤ ∫⁻ x in S, incidenceDuration E x ∂ν :=
      lintegral_mono_set inter_subset_left

end Submission.Obl.k4_initial_horizon_bound
