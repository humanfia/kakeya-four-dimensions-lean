/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/MixtureBands.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.DensityBands
import Submission.Obl.k4_native_grid_profile_extension.DensityEquiv

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

local instance mixtureBandsPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance mixtureBandsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- Sums of exact observation densities are exact densities for sums of atoms. -/
theorem finite_observation_density {ι Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (ρ : Measure Y) (ν : ι → Measure Ω) (T : Finset ι) (Q : Ω → Y) (hQ : Measurable Q)
    (f : ι → Y → ℝ≥0∞) (hf : ∀ a, Measurable (f a))
    (hlaw : ∀ a, (ν a).map Q = ρ.withDensity (f a)) :
    (∑ a ∈ T, ν a).map Q = ρ.withDensity (fun y => ∑ a ∈ T, f a y) := by
  rw [Measure.map_finset_sum hQ.aemeasurable]
  simp_rw [hlaw]
  ext A hA
  rw [Measure.finsetSum_apply, withDensity_apply _ hA, lintegral_finsetSum _ (fun a _ => hf a)]
  exact Finset.sum_congr rfl (fun a _ => withDensity_apply _ hA)

/-- The record-band estimate for an actual incidence law, independent of the
chosen version of its observation density. -/
theorem finite_mixture_band {ι κ Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (ρ : Measure Y) [SigmaFinite ρ] (ν : ι → Measure Ω)
    (I T : Finset ι) (hT : T ⊆ I) (w : ι → ℝ≥0∞) (code : ι → κ) (S : κ → Set Y)
    (Q : Ω → Y) (hQ : Measurable Q) (hS : ∀ c, MeasurableSet (S c))
    (hkernels : ∀ a, ∃ f : Y → ℝ≥0∞, Measurable f ∧
      (ν a).map Q = ρ.withDensity f ∧ ∀ y, f y ≤ (S (code a)).indicator (fun _ => w a) y)
    (A D lower upper ε : ℝ≥0∞)
    (hvol : ∀ c ∈ T.image code, ρ (S c) ≤ A)
    (hoverlap : ∀ y, ((T.image code).filter (fun c => y ∈ S c)).card ≤ D)
    (hlower : ∀ c ∈ T.image code, lower ≤ recordMass I w code c)
    (hupper : ∀ c ∈ T.image code, recordMass I w code c ≤ upper) :
    ∃ f : Y → ℝ≥0∞, Measurable f ∧ (∑ a ∈ T, ν a).map Q = ρ.withDensity f ∧
      ∀ g : Y → ℝ≥0∞, Measurable g → (∑ a ∈ T, ν a).map Q = ρ.withDensity g →
        (∑ a ∈ T, ν a) {p | g (Q p) < ε * lower ∨ D * upper < g (Q p)} ≤
          ε * A * ∑ a ∈ I, w a := by
  classical
  choose f hf hlaw hcap using hkernels
  let F : Y → ℝ≥0∞ := fun y => ∑ a ∈ T, f a y
  have hF : Measurable F := by fun_prop
  have hFlaw := finite_observation_density ρ ν T Q hQ f hf hlaw
  refine ⟨F, hF, hFlaw, ?_⟩
  intro g hg hglaw
  have hband := atom_density_band ρ I T hT w code S f hf hS A D lower upper ε
    hvol hoverlap (fun a _ => hcap a) hlower hupper
  have hbad : MeasurableSet {y | F y < ε * lower ∨ D * upper < F y} :=
    (measurableSet_lt hF measurable_const).union (measurableSet_lt measurable_const hF)
  have hsrc : (∑ a ∈ T, ν a) {p | F (Q p) < ε * lower ∨ D * upper < F (Q p)} ≤
      ε * A * ∑ a ∈ I, w a := by
    change (∑ a ∈ T, ν a) (Q ⁻¹' {y | F y < ε * lower ∨ D * upper < F y}) ≤ _
    rw [← Measure.map_apply hQ hbad, hFlaw]
    exact hband
  rw [Submission.Obl.k4_native_grid_profile_extension.observation_density_bad_mass_eq
    (∑ a ∈ T, ν a) ρ Q hQ g F hg hF hglaw hFlaw (ε * lower) (D * upper)]
  exact hsrc

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
