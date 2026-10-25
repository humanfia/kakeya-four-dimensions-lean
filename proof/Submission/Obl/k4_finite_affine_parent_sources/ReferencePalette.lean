-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_scalar_guarded_tangent_preparation.CodeVelocity
import Submission.Obl.k4_scalar_guarded_tangent_preparation.SmoothedFrostman
import Submission.Obl.k4_scalar_guarded_tangent_preparation.VelocityReadoutAE

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace ReferencePalette

open Submission.Obl.k4_scalar_guarded_tangent_preparation

/-- Blur the original finite-code probabilities once. The weights are
those of the reference law, before any likelihood or label restriction. -/
def law {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) (U : Ω → ι) (center : ι → ℝ) (δ : ℝ) : Measure ℝ :=
  scatterPalette (fun i => μ.real (U ⁻¹' {i})) center δ

theorem probability {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ι) (hU : Measurable U)
    (center : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    IsProbabilityMeasure (law μ U center δ) := by
  obtain ⟨hp, hp1, -⟩ := finite_code_probabilities μ U hU
  exact scatterPalette_probability _ _ hδ hp hp1

/-- Angular ceilings under the original parent probability transfer to
every coarser bin of the same fixed palette. -/
theorem bin_cap {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ι) (hU : Measurable U)
    (V : Ω → ℝ) (center : ι → ℝ) {δ width : ℝ}
    (hδ : 0 < δ) (hwidth : 2 * δ ≤ width)
    (hclose : ∀ᵐ x ∂μ, |V x - center (U x)| ≤ δ)
    (C : ℝ≥0∞) (hcap : ∀ j : ℤ, μ {x | ⌊V x / width⌋ = j} ≤ C) (e : ℤ) :
    law μ U center δ {v | ⌊v / width⌋ = e} ≤ 6 * C := by
  exact smoothed_floor_bin_cap μ U hU V _ center hδ hwidth
    (fun _ => ENNReal.ofReal_toReal (measure_ne_top _ _)) hclose C hcap e

/-- All later numerators use the same predeletion code probabilities.
The current law can be any submeasure for which the code ceiling holds. -/
theorem joint_bin_cap {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ ρ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → ι)
    (V : Ω → ℝ) (center : ι → ℝ) {δ width : ℝ}
    (hδ : 0 < δ) (hwidth : 2 * δ ≤ width)
    (P : Set Ω) (C : ℝ≥0∞)
    (hclose : ∀ᵐ x ∂ρ, |V x - center (U x)| ≤ δ)
    (hcap : ∀ i, ρ (P ∩ U ⁻¹' {i}) ≤ C * μ (U ⁻¹' {i})) (e : ℤ) :
    ρ (P ∩ {x | ⌊V x / width⌋ = e}) ≤
      4 * C * law μ U center δ {v | ⌊v / width⌋ = e} := by
  apply joint_floor_bin_from_fine_cells_ae ρ U V _ center hδ hwidth P C hclose
  intro i
  rw [ofReal_measureReal (measure_ne_top _ _)]
  exact hcap i

/-- A half-radius enlargement under the original parent law is charged
to one palette bin, including its boundary points. -/
theorem enlarged_interval {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ι) (hU : Measurable U)
    (V : Ω → ℝ) (center : ι → ℝ) {δ a b : ℝ}
    (hδ : 0 < δ) (hwidth : 2 * δ ≤ b - a)
    (hclose : ∀ᵐ x ∂μ, |V x - center (U x)| ≤ δ / 2) :
    μ (V ⁻¹' Icc (a - δ / 2) (b + δ / 2)) ≤
      4 * law μ U center δ (Ico a b) := by
  classical
  let s := Finset.univ.filter (fun i => a - δ ≤ center i ∧ center i ≤ b + δ)
  have hsub : μ (V ⁻¹' Icc (a - δ / 2) (b + δ / 2)) ≤ μ (U ⁻¹' (s : Set ι)) := by
    apply measure_mono_ae
    filter_upwards [hclose] with x hx
    intro hxV
    have hnear := abs_le.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      constructor <;> linarith [hxV.1, hxV.2]⟩
  have hsum : μ (U ⁻¹' (s : Set ι)) = ∑ i ∈ s, ENNReal.ofReal (μ.real (U ⁻¹' {i})) := by
    rw [Finset.sum_congr rfl (fun i _ => ofReal_measureReal (measure_ne_top μ (U ⁻¹' {i})))]
    exact (sum_measure_preimage_singleton s (fun i _ => hU (measurableSet_singleton i))).symm
  rw [hsum] at hsub
  exact hsub.trans (old_palette_cells_le_four_smoothed _ center hδ hwidth s
    (fun i hi => (Finset.mem_filter.mp hi).2))

end ReferencePalette

end
end Submission.Obl.k4_finite_affine_parent_sources
