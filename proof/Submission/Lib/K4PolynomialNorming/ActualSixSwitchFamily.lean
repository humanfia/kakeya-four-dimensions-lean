/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.ActualNormalizedSwitching
import Submission.Lib.K4PolynomialNorming.StationarySixSwitchFamily

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching

/-- Original rectangular caps, conditional breadth and long-line time
ceilings yield an actual substantial six-switch parameter family. The
endpoint support is charged under that same unnormalized path law. -/
theorem actual_substantial_six_basis_switch_family {L Q C : Type*}
    [MeasurableSpace L] [MeasurableSpace Q] [MeasurableSpace C]
    [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSingletonClass C] [Countable C] [StandardBorelSpace C] [Nonempty C]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    [IsProbabilityMeasure (ν ⊗ₘ κ)]
    (state : L × ℝ → Q) (hstate : Measurable state)
    (control : L → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 < r)
    (Long : Set L) (hLong : MeasurableSet Long)
    (Good : Set (L × ℝ)) (hGood : MeasurableSet Good)
    (w₀ : L × ℝ → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ z, w₀ z ≤ 1)
    (hwGood : ∀ z, w₀ z ≠ 0 → z ∈ Good)
    (μ : Measure (L × ℝ)) [SFinite μ] (π : Measure C) [SigmaFinite π]
    (K D p b : ENNReal) (a h U : ℝ) (hh : 0 < h)
    (hzero : (ν ⊗ₘ κ).withDensity w₀ ≤ μ)
    (hrect : ∀ q (A : Set C), MeasurableSet A →
      (ν ⊗ₘ κ) {z | state z = q ∧ control z.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
    (htime : ∀ l ∈ Long, κ l ≤ ((ENNReal.ofReal h)⁻¹ * D) • (volume : Measure ℝ))
    (hbroad : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ W < 3 →
        (conditionalResampling (ν ⊗ₘ κ) state hstate z).map (fun y => control y.1)
          {c | Metric.infDist (v c) (W : Set _) < r} ≤ p)
    (ht : ∀ᵐ z ∂ν ⊗ₘ κ, z.2 ∈ Icc a (a+h))
    (hv : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ j, |v (control z.1) j| ≤ U)
    (F : Set (((L × ℝ) × (Fin 6 → C)) × ((Fin 5 → ℝ) × ℝ)))
    (hF : MeasurableSet F)
    (htarget : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity (fun x =>
      causalRetentionWeights w₀
        (basisPencilRetention (fun z => control z.1) v r (Prod.fst ⁻¹' Long)) 6
          (Preorder.frestrictLe 6 x)), sixSwitchCoordinates control a h x ∈ F)
    (hpositive : (K*D)^6 * (μ.prod (Measure.pi (fun _ : Fin 6 => π))) univ * b +
      6 * ((ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ+p) < ((ν ⊗ₘ κ).withDensity w₀) univ) :
    ∃ row, ∃ A : Set (Fin 6 → ℝ), MeasurableSet A ∧ b < volume A ∧
      ∀ δ ∈ A, (row,splitHeadCoordinates 5 δ) ∈
        sixSwitchCertificates Good v (r^3) U ∩ F := by
  let S := stateTimeSwitch ν κ state hstate
  letI := stateTimeSwitch_markov ν κ state hstate
  have hs : S ∘ₘ (ν ⊗ₘ κ) = ν ⊗ₘ κ := stateTimeSwitch_invariant ν κ state hstate
  have hp := conditionalResampling_palette_le (ν ⊗ₘ κ) state hstate
    (fun z => control z.1) (hcontrol.comp measurable_fst) π K hrect
  have hc := actual_switch_restricted_normalized_observation_le ν κ state hstate control hcontrol
    π Long hLong K D a h hh hp htime
  have hbreadth : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ W < 3 →
        (S z).map (fun y => control y.1) {c | Metric.infDist (v c) (W : Set _) < r} ≤ p := by
    filter_upwards [hbroad] with z hz
    have heq := congrArg (fun k : Kernel (L × ℝ) C => k z)
      (refreshed_control_kernel (conditionalResampling (ν ⊗ₘ κ) state hstate)
        κ control hcontrol)
    have hmap : (S z).map (fun y => control y.1) =
        (conditionalResampling (ν ⊗ₘ κ) state hstate z).map (fun y => control y.1) := by
      rw [Kernel.map_apply _ (show Measurable (fun y : L × ℝ => control y.1) from
        hcontrol.comp measurable_fst),
        Kernel.map_apply _ (show Measurable (fun y : L × ℝ => control y.1) from
          hcontrol.comp measurable_fst)] at heq
      exact heq
    intro W hW
    rw [hmap]
    exact hz W hW
  exact stationary_substantial_six_basis_switch_family (ν ⊗ₘ κ) S hs control hcontrol v r hr
    (Prod.fst ⁻¹' Long) Good (hLong.preimage measurable_fst) hGood w₀ hw₀ hw₀1 hwGood
    μ π (K*D) p b a h U hh hzero hc hbreadth ht hv F hF htarget hpositive

end Submission.Lib.K4PolynomialNorming
