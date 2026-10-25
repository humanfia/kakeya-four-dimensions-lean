/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.ActualRetainedSwitching
import Submission.Lib.K4PolynomialNorming.StationaryWeightedSupport

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching

/-- Geometric shared-state certificates only need to hold on an original
almost-sure support. The intermediate conditional redraw stays in that
support before its time coordinate is refreshed. -/
theorem actualSwitchedPathMeasure_weighted_ae_line_relations_of_original_support {L Q : Type*}
    [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace Q] [StandardBorelSpace Q]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    [IsProbabilityMeasure (ν ⊗ₘ κ)]
    (state : L × ℝ → Q) (hstate : Measurable state)
    (w : (ℕ → L × ℝ) → ENNReal)
    (R : (L × ℝ) → L → Prop)
    (hR : MeasurableSet {z : (L × ℝ) × L | R z.1 z.2})
    (Valid : L × ℝ → Prop) (hValid : ∀ᵐ z ∂ν ⊗ₘ κ, Valid z)
    (hcert : ∀ z y, state y = state z → Valid z → Valid y → R z y.1) :
    ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity w,
      ∀ n, R (x n) (x (n+1)).1 := by
  let P := ν ⊗ₘ κ
  let A := conditionalResampling P state hstate
  letI : IsMarkovKernel A := conditionalResampling_markov P state hstate
  let S := stateTimeSwitch ν κ state hstate
  letI := stateTimeSwitch_markov ν κ state hstate
  have hstep : ∀ᵐ z ∂P, ∀ᵐ y ∂S z, R z y.1 :=
    stationary_redraw_refresh_ae_relation P A (lineRefreshKernel κ)
      (conditionalResampling_invariant P state hstate) state Prod.fst measurable_fst
      (conditionalResampling_ae_key P state hstate) (lineRefreshKernel_ae_line κ)
      R hR Valid hValid hcert
  exact kernelPathMeasure_weighted_ae_steps P (fun _ => S)
    (fun _ => stateTimeSwitch_invariant ν κ state hstate) w
    (fun _ => {z : (L × ℝ) × (L × ℝ) | R z.1 z.2.1})
    (fun _ => hR.preimage (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
    (fun _ => hstep)

/-- Every shared-state geometric relation holds on every actual switched
leg after arbitrary retention, with the original conditional coupling. -/
theorem actualSwitchedPathMeasure_weighted_ae_line_relations {L Q : Type*}
    [MeasurableSpace L] [MeasurableSingletonClass L]
    [MeasurableSpace Q] [StandardBorelSpace Q]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    [IsProbabilityMeasure (ν ⊗ₘ κ)]
    (state : L × ℝ → Q) (hstate : Measurable state)
    (w : (ℕ → L × ℝ) → ENNReal)
    (R : (L × ℝ) → L → Prop)
    (hR : MeasurableSet {z : (L × ℝ) × L | R z.1 z.2})
    (hcert : ∀ z y, state y = state z → R z y.1) :
    ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity w,
      ∀ n, R (x n) (x (n+1)).1 := by
  let S := stateTimeSwitch ν κ state hstate
  letI := stateTimeSwitch_markov ν κ state hstate
  have hrel := stateTimeSwitch_ae_line_relation ν κ state hstate R
    (fun z => hR.preimage (measurable_const.prodMk measurable_id)) hcert
  exact kernelPathMeasure_weighted_ae_steps (ν ⊗ₘ κ) (fun _ => S)
    (fun _ => stateTimeSwitch_invariant ν κ state hstate) w
    (fun _ => {z : (L × ℝ) × (L × ℝ) | R z.1 z.2.1})
    (fun _ => hR.preimage (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
    (fun _ => hrel)

end Submission.Lib.K4PolynomialNorming
