/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/DensityEquiv.lean. Earlier source attributions are retained below.
-/

import Mathlib

/-!
# Density transport by measurable equivalences
-/

namespace Submission.Obl.k4_native_grid_profile_extension

open Set MeasureTheory
open scoped ENNReal

/-- Transport a density through a measure-preserving measurable equivalence. -/
theorem map_withDensity_equiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (e : A ≃ᵐ B) (he : MeasurePreserving e μ ν)
    (g : A → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity g).map e = ν.withDensity (fun b => g (e.symm b)) := by
  ext S hS
  rw [Measure.map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    withDensity_apply _ hS]
  simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using
    he.setLIntegral_comp_preimage hS (hg.comp e.symm.measurable)

/-- Two measurable representatives of an observation density agree almost
 everywhere on the original state space. -/
theorem observation_density_ae_eq {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SigmaFinite ν]
    (Q : A → B) (hQ : Measurable Q) (f g : B → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfmap : μ.map Q = ν.withDensity f) (hgmap : μ.map Q = ν.withDensity g) :
    ∀ᵐ a ∂μ, f (Q a) = g (Q a) := by
  have hfg : f =ᵐ[ν] g :=
    (withDensity_eq_iff_of_sigmaFinite hf.aemeasurable hg.aemeasurable).mp
      (hfmap.symm.trans hgmap)
  have hfg' : f =ᵐ[ν.withDensity f] g := (withDensity_absolutelyContinuous _ _) hfg
  rw [← hfmap] at hfg'
  exact (ae_map_iff hQ.aemeasurable (measurableSet_eq_fun hf hg)).mp hfg'

/-- Exceptional sets defined by a density are independent of its representative. -/
theorem observation_density_bad_mass_eq {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SigmaFinite ν]
    (Q : A → B) (hQ : Measurable Q) (f g : B → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfmap : μ.map Q = ν.withDensity f) (hgmap : μ.map Q = ν.withDensity g)
    (lo hi : ℝ≥0∞) :
    μ {a | f (Q a) < lo ∨ hi < f (Q a)} =
      μ {a | g (Q a) < lo ∨ hi < g (Q a)} := by
  apply measure_congr
  filter_upwards [observation_density_ae_eq μ ν Q hQ f g hf hg hfmap hgmap] with a ha
  simp only [ha]

end Submission.Obl.k4_native_grid_profile_extension
