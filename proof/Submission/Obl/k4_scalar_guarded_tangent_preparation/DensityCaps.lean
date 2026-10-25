import Mathlib

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

/-- A ceiling imposed on the original observation density bounds the
restricted observation law with its original reference measure. -/
theorem observation_density_ceiling
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) (baseMeasure : Measure Y) (Q : Ω → Y) (hQ : Measurable Q)
    (f : Y → ℝ≥0∞) (hf : Measurable f) (C : ℝ≥0∞)
    (hlaw : μ.map Q = baseMeasure.withDensity f) :
    (μ.restrict {ω | f (Q ω) ≤ C}).map Q ≤ C • baseMeasure := by
  let S : Set Y := {y | f y ≤ C}
  have hS : MeasurableSet S := measurableSet_le hf measurable_const
  change (μ.restrict (Q ⁻¹' S)).map Q ≤ C • baseMeasure
  rw [← Measure.restrict_map hQ hS, hlaw, restrict_withDensity hS,
    ← withDensity_indicator hS, ← withDensity_const]
  apply withDensity_mono
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy]
      exact hy
    · simp only [indicator_of_notMem hy, zero_le]

/-- Every later incidence mask preserves a ceiling prepared using the
unchanged original observation law. -/
theorem submeasure_observation_density_ceiling
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {μ ρ : Measure Ω} (baseMeasure : Measure Y) (Q : Ω → Y) (hQ : Measurable Q)
    (f : Y → ℝ≥0∞) (hf : Measurable f) (C : ℝ≥0∞)
    (hlaw : μ.map Q = baseMeasure.withDensity f)
    (hρ : ρ ≤ μ.restrict {ω | f (Q ω) ≤ C}) :
    ρ.map Q ≤ C • baseMeasure :=
  (Measure.map_mono hρ hQ).trans (observation_density_ceiling μ baseMeasure Q hQ f hf C hlaw)

/-- A rectangular observation bound can be evaluated in original units,
without conditioning on the retained incidence mass. -/
theorem observation_cell_le
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {ρ : Measure Ω} {baseMeasure : Measure Y} {Q : Ω → Y} (hQ : Measurable Q)
    {C : ℝ≥0∞} (hcap : ρ.map Q ≤ C • baseMeasure)
    {B : Set Y} (hB : MeasurableSet B) :
    ρ (Q ⁻¹' B) ≤ C * baseMeasure B := by
  rw [← Measure.map_apply hQ hB]
  exact hcap B

end Submission.Obl.k4_scalar_guarded_tangent_preparation
