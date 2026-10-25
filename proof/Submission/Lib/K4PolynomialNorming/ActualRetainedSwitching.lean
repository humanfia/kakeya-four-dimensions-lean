/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.StationaryObservedCaps
import Submission.Lib.K4ScalarActualSwitching.CompleteSwitch
import Submission.Lib.K4ScalarActualSwitching.PaletteConditioning

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching

/-- The unrestricted trajectory of the genuine state-conditional redraw
followed by the line-preserving endpoint-time refresh. -/
noncomputable def actualSwitchedPathMeasure {L Q : Type*}
    [MeasurableSpace L] [MeasurableSpace Q]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    (state : L × ℝ → Q) (hstate : Measurable state) : Measure (ℕ → L × ℝ) := by
  letI := stateTimeSwitch_markov ν κ state hstate
  exact kernelPathMeasure (ν ⊗ₘ κ) (fun _ => stateTimeSwitch ν κ state hstate)

/-- Prepared rectangular caps under the original incidence law and time
ceilings on long lines give the observed law of any finite number of
genuine retained switches. The retention may depend on the complete past. -/
theorem actual_retained_switch_observed_law {L Q V Ω : Type*}
    [MeasurableSpace L] [MeasurableSpace Q] [MeasurableSpace V] [MeasurableSpace Ω]
    [MeasurableSingletonClass Q] [Countable Q]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    [StandardBorelSpace V] [Nonempty V]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    [IsProbabilityMeasure (ν ⊗ₘ κ)]
    (state : L × ℝ → Q) (hstate : Measurable state)
    (control : L → V) (hcontrol : Measurable control)
    (π : Measure V) [SigmaFinite π] (Long : Set L) (hLong : MeasurableSet Long)
    (K D : ENNReal)
    (hrect : ∀ q (A : Set V), MeasurableSet A →
      (ν ⊗ₘ κ) {z | state z = q ∧ control z.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
    (htime : ∀ l ∈ Long, κ l ≤ D • (volume : Measure ℝ))
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
          (fun _ z => (control z.2.1, z.2.2)) N (Preorder.frestrictLe N x)) ≤
      (K * D) ^ N • (μ.prod (Measure.pi (fun _ : Fin N => π.prod (volume : Measure ℝ)))) := by
  let S := stateTimeSwitch ν κ state hstate
  letI := stateTimeSwitch_markov ν κ state hstate
  have hs : S ∘ₘ (ν ⊗ₘ κ) = ν ⊗ₘ κ := stateTimeSwitch_invariant ν κ state hstate
  have hp := conditionalResampling_palette_le (ν ⊗ₘ κ) state hstate
    (fun z => control z.1) (hcontrol.comp measurable_fst) π K hrect
  have hc := stateTimeSwitch_restricted_control_time_le ν κ state hstate control hcontrol
    π (volume : Measure ℝ) Long hLong K D hp htime
  exact stationary_retained_observed_process_domination (ν ⊗ₘ κ) S hs
    w₀ hw₀ hw₀1 α hα (Prod.fst ⁻¹' Long) (hLong.preimage measurable_fst) hretain
    start hstart (Prod.map control id) (hcontrol.prodMap measurable_id)
    μ (π.prod volume) (K * D) hzero hc N

end Submission.Lib.K4PolynomialNorming


namespace Submission.Lib.K4PolynomialNorming

open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching

/-- Original short-line mass and history-selected palette pencils bound
the loss of a genuine switching trajectory, for any finite number of steps. -/
theorem actual_retained_switch_mass_bound {L Q V : Type*}
    [MeasurableSpace L] [MeasurableSpace Q] [MeasurableSpace V]
    [MeasurableSingletonClass Q] [Countable Q]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    [StandardBorelSpace V] [Nonempty V]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    [IsProbabilityMeasure (ν ⊗ₘ κ)]
    (state : L × ℝ → Q) (hstate : Measurable state)
    (control : L → V) (hcontrol : Measurable control)
    (π : Measure V) (K : ENNReal)
    (hrect : ∀ q (A : Set V), MeasurableSet A →
      (ν ⊗ₘ κ) {z | state z = q ∧ control z.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
    (Long : Set L) (hLong : MeasurableSet Long)
    (w₀ : L × ℝ → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ z, w₀ z ≤ 1)
    (α : (n : ℕ) → ((i : Finset.Iic n) → L × ℝ) → L × ℝ → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n))) (hα1 : ∀ n h z, α n h z ≤ 1)
    (A : (n : ℕ) → Set ((((i : Finset.Iic n) → L × ℝ)) × V))
    (hA : ∀ n, MeasurableSet (A n)) (p : ℕ → ENNReal)
    (hthin : ∀ n h, π (Prod.mk h ⁻¹' A n) ≤ p n)
    (hdefect : ∀ n h z, 1 - α n h z ≤
      (Prod.fst ⁻¹' Long)ᶜ.indicator (fun _ => 1) z +
        (A n).indicator (fun _ => 1) (h,control z.1)) (N : ℕ) :
    ((ν ⊗ₘ κ).withDensity w₀) univ ≤
      ((actualSwitchedPathMeasure ν κ state hstate).withDensity (fun x =>
        causalRetentionWeights w₀ α N (Preorder.frestrictLe N x))) univ +
      ∑ n ∈ Finset.range N, ((ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ + K * p n) := by
  let S := stateTimeSwitch ν κ state hstate
  letI := stateTimeSwitch_markov ν κ state hstate
  have hs : S ∘ₘ (ν ⊗ₘ κ) = ν ⊗ₘ κ := stateTimeSwitch_invariant ν κ state hstate
  have hp := conditionalResampling_palette_le (ν ⊗ₘ κ) state hstate
    (fun z => control z.1) (hcontrol.comp measurable_fst) π K hrect
  have hc : ∀ᵐ z ∂ν ⊗ₘ κ, (S z).map (fun y => control y.1) ≤ K • π := by
    filter_upwards [hp] with z hz
    have heq := congrArg (fun k : Kernel (L × ℝ) V => k z)
      (refreshed_control_kernel (conditionalResampling (ν ⊗ₘ κ) state hstate)
        κ control hcontrol)
    have hmap : (S z).map (fun y => control y.1) =
        (conditionalResampling (ν ⊗ₘ κ) state hstate z).map (fun y => control y.1) := by
      rw [Kernel.map_apply _ (show Measurable (fun y : L × ℝ => control y.1) from
        hcontrol.comp measurable_fst),
        Kernel.map_apply _ (show Measurable (fun y : L × ℝ => control y.1) from
          hcontrol.comp measurable_fst)] at heq
      exact heq
    rw [hmap]
    exact hz
  exact stationary_causal_retention_mass_bound (ν ⊗ₘ κ) S hs w₀ hw₀ hw₀1 α hα hα1
    (Prod.fst ⁻¹' Long) (hLong.preimage measurable_fst)
    (fun z => control z.1) (hcontrol.comp measurable_fst) π K hc A hA p hthin hdefect N

end Submission.Lib.K4PolynomialNorming
