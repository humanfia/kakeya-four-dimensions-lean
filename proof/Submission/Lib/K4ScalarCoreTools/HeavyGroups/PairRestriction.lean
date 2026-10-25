/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarHeavyGroups/PairRestriction.lean at aca48c1.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit af6b1867dfbb677a4a0e008effa5b557d8531e7f,
Submission/Obl/k4_scalar_mesh_projection/PairRestriction.lean.
-/

import Mathlib

namespace Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Set MeasureTheory

/-- Pair breadth survives a restriction which retains a fixed fraction of
its original state mass. All measures stay unnormalized. -/
theorem pair_mass_of_original_cap_and_fraction {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (T : Set (Ω × Ω)) (hT : MeasurableSet T)
    (p δ : ℝ) (hp : 0 ≤ p) (hδ : 0 ≤ δ) (hsmall : 2 * p ≤ δ)
    (hdom : ν ≤ μ) (hfloor : ENNReal.ofReal δ * μ univ ≤ ν univ)
    (hcap : ∀ x, μ (Prod.mk x ⁻¹' T) ≤ ENNReal.ofReal p * μ univ) :
    ENNReal.ofReal ((ν univ).toReal ^ 2 / 2) ≤ (ν.prod ν) Tᶜ := by
  have hbad : (ν.prod ν) T ≤ ENNReal.ofReal p * μ univ * ν univ := by
    rw [Measure.prod_apply hT]
    calc
      _ ≤ ∫⁻ _x, ENNReal.ofReal p * μ univ ∂ν := lintegral_mono fun x =>
        (hdom _).trans (hcap x)
      _ = _ := by rw [lintegral_const]
  have hbadR := ENNReal.toReal_mono (by finiteness) hbad
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp] at hbadR
  have hfloorR := ENNReal.toReal_mono (measure_ne_top ν univ) hfloor
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ] at hfloorR
  have hpm : 2 * p * (μ univ).toReal ≤ (ν univ).toReal :=
    (mul_le_mul_of_nonneg_right hsmall ENNReal.toReal_nonneg).trans hfloorR
  have hpmul := mul_le_mul_of_nonneg_right hpm (show 0 ≤ (ν univ).toReal from ENNReal.toReal_nonneg)
  have hpartition : ((ν.prod ν) T).toReal + ((ν.prod ν) Tᶜ).toReal = (ν univ).toReal ^ 2 := by
    have h := congrArg ENNReal.toReal (measure_add_measure_compl (μ := ν.prod ν) hT)
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h
    simpa [← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul, pow_two] using h
  have hreal : (ν univ).toReal ^ 2 / 2 ≤ ((ν.prod ν) Tᶜ).toReal := by nlinarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top (ν.prod ν) Tᶜ)]
  exact ENNReal.ofReal_le_ofReal hreal

end Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
