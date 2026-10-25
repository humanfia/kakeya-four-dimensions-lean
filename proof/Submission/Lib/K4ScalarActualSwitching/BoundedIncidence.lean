/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 0c45d28d585d2de5a8ca76061eed464a2d8c1f06,
Submission/Obl/k4_scalar_mesh_projection/BoundedIncidence.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarSwitching.Resampling
import Submission.Lib.K4Homogenization.RetainedDuration

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

/-- A bounded original incidence density supplies its actual normalized
time kernel. The line marginal remains the unnormalized original one;
the short-row loss is charged to the unchanged trajectory prior. -/
theorem bounded_incidence_disintegration {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [IsFiniteMeasure ν] (τ : Measure T) [IsProbabilityMeasure τ]
    (F : X × T → ENNReal) (hF : Measurable F)
    (H : ENNReal) (hH : H ≠ ∞) (hbound : ∀ z, F z ≤ H) :
    let μ := (ν.prod τ).withDensity F
    IsFiniteMeasure μ ∧ ∃ κ : Kernel X T, IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ ∧
      (∀ q : ENNReal, 0 < q → ∀ x ∈ Submission.Lib.K4Homogenization.durationRetained τ F univ q,
        κ x ≤ (H / q) • τ) ∧
      (∀ q : ENNReal, μ (Prod.fst ⁻¹'
        (Submission.Lib.K4Homogenization.durationRetained τ F univ q)ᶜ) ≤ q * ν univ) := by
  let μ := (ν.prod τ).withDensity F
  have hdom : μ ≤ H • ν.prod τ := by
    simpa only [withDensity_const] using withDensity_mono (ae_of_all _ hbound)
  have htotal : (ν.prod τ) univ = ν univ := by
    rw [← univ_prod_univ, Measure.prod_prod, (measure_univ : τ univ = 1), mul_one]
  have hmass : μ univ ≤ H * ν univ := by
    simpa only [Measure.smul_apply, smul_eq_mul, htotal] using
      Measure.le_iff.mp hdom univ MeasurableSet.univ
  have hfin : IsFiniteMeasure μ := ⟨hmass.trans_lt
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hH) (measure_lt_top ν univ))⟩
  have hrow (x : X) : (∫⁻ t, F (x, t) ∂τ) ≠ ∞ := by
    apply ne_of_lt
    calc
      (∫⁻ t, F (x, t) ∂τ) ≤ ∫⁻ _t, H ∂τ := lintegral_mono fun t => hbound (x, t)
      _ = H := by simp
      _ < ∞ := lt_top_iff_ne_top.mpr hH
  let κ := normalizedFiberKernel τ F
  letI : IsMarkovKernel κ := normalizedFiberKernel_markov τ F hF hrow
  have hjoint := normalizedFiberKernel_joint_law ν τ F hF hrow
  have hfst := congrArg Measure.fst hjoint
  rw [Measure.fst_compProd] at hfst
  refine ⟨hfin, κ, inferInstance, ?_, ?_, ?_⟩
  · rw [← hfst]
    exact hjoint
  · intro q hq x hx
    apply normalizedFiberKernel_le_of_duration_floor τ F hF H q hq x
      (ae_of_all _ fun t => hbound (x, t))
    simpa only [Submission.Lib.K4Homogenization.durationRetained, mem_ofPred_eq,
      Submission.Lib.K4Homogenization.incidenceDuration, Measure.restrict_univ] using hx
  · intro q
    have h := Submission.Lib.K4Homogenization.duration_omission_mass_le ν τ hF MeasurableSet.univ q
    simpa only [Set.prod_univ, μ] using h

end Submission.Lib.K4ScalarActualSwitching
