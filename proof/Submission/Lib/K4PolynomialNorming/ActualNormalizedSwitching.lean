/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.ActualRetainedSwitching
import Submission.Lib.K4PolynomialNorming.NormalizedSwitchingCoordinates

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching

/-- The genuine restricted switch has its palette/time ceiling in unit
block coordinates, with the physical time-density factor canceled. -/
theorem actual_switch_restricted_normalized_observation_le {L Q V : Type*}
    [MeasurableSpace L] [MeasurableSpace Q] [MeasurableSpace V]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    (state : L × ℝ → Q) (hstate : Measurable state)
    (control : L → V) (hcontrol : Measurable control)
    (π : Measure V) [SigmaFinite π] (Long : Set L) (hLong : MeasurableSet Long)
    (K D : ENNReal) (a h : ℝ) (hh : 0 < h)
    (hpalette : ∀ᵐ z ∂ν ⊗ₘ κ,
      (conditionalResampling (ν ⊗ₘ κ) state hstate z).map (fun y => control y.1) ≤ K • π)
    (htime : ∀ l ∈ Long, κ l ≤ ((ENNReal.ofReal h)⁻¹ * D) • (volume : Measure ℝ)) :
    ∀ᵐ z ∂ν ⊗ₘ κ,
      ((stateTimeSwitch ν κ state hstate z).restrict (Prod.fst ⁻¹' Long)).map
        (fun y => (control y.1, (y.2-a)/h)) ≤ (K * D) • π.prod (volume : Measure ℝ) := by
  have hraw := stateTimeSwitch_restricted_control_time_le ν κ state hstate control hcontrol
    π (volume : Measure ℝ) Long hLong K ((ENNReal.ofReal h)⁻¹ * D) hpalette htime
  filter_upwards [hraw] with z hz
  have hn := normalize_control_time_ceiling π _ K D a h hh hz
  rw [Measure.map_map
    (f := Prod.map control (id : ℝ → ℝ))
    (g := Prod.map (id : V → V) (fun t : ℝ => (t-a)/h))
    (by fun_prop) (hcontrol.prodMap measurable_id)] at hn
  exact hn

/-- Prepared original rectangular caps and physical long-line time
ceilings give an arbitrary finite observed law in normalized time. -/
theorem actual_retained_switch_normalized_observed_law {L Q V Ω : Type*}
    [MeasurableSpace L] [MeasurableSpace Q] [MeasurableSpace V] [MeasurableSpace Ω]
    [MeasurableSingletonClass Q] [Countable Q]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    [StandardBorelSpace V] [Nonempty V]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    [IsProbabilityMeasure (ν ⊗ₘ κ)]
    (state : L × ℝ → Q) (hstate : Measurable state)
    (control : L → V) (hcontrol : Measurable control)
    (π : Measure V) [SigmaFinite π] (Long : Set L) (hLong : MeasurableSet Long)
    (K D : ENNReal) (a h : ℝ) (hh : 0 < h)
    (hrect : ∀ q (A : Set V), MeasurableSet A →
      (ν ⊗ₘ κ) {z | state z = q ∧ control z.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
    (htime : ∀ l ∈ Long, κ l ≤ ((ENNReal.ofReal h)⁻¹ * D) • (volume : Measure ℝ))
    (w₀ : L × ℝ → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ z, w₀ z ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → L × ℝ) → L × ℝ → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n)))
    (hretain : ∀ n h z, α n h z ≤ (Prod.fst ⁻¹' Long).indicator (fun _ => 1) z)
    (start : L × ℝ → Ω) (hstart : Measurable start)
    (μ : Measure Ω) [SFinite μ]
    (hzero : ((ν ⊗ₘ κ).withDensity w₀).map start ≤ μ) (N : ℕ) :
    ((actualSwitchedPathMeasure ν κ state hstate).withDensity (fun x =>
      causalRetentionWeights w₀ α N (Preorder.frestrictLe N x))).map
        (fun x => causalObservedHistory start
          (fun _ z => (control z.2.1, (z.2.2-a)/h)) N (Preorder.frestrictLe N x)) ≤
      (K * D) ^ N • (μ.prod (Measure.pi (fun _ : Fin N => π.prod (volume : Measure ℝ)))) := by
  let S := stateTimeSwitch ν κ state hstate
  letI := stateTimeSwitch_markov ν κ state hstate
  have hs : S ∘ₘ (ν ⊗ₘ κ) = ν ⊗ₘ κ := stateTimeSwitch_invariant ν κ state hstate
  have hp := conditionalResampling_palette_le (ν ⊗ₘ κ) state hstate
    (fun z => control z.1) (hcontrol.comp measurable_fst) π K hrect
  have hc := actual_switch_restricted_normalized_observation_le ν κ state hstate control hcontrol
    π Long hLong K D a h hh hp htime
  exact stationary_retained_observed_process_domination (ν ⊗ₘ κ) S hs
    w₀ hw₀ hw₀1 α hα (Prod.fst ⁻¹' Long) (hLong.preimage measurable_fst) hretain
    start hstart (fun z => (control z.1, (z.2-a)/h)) (by fun_prop)
    μ (π.prod volume) (K * D) hzero hc N

end Submission.Lib.K4PolynomialNorming
