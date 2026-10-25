/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.ActualSixSwitchFamily
import Submission.Lib.K4PolynomialNorming.CodedSixSwitchEndpoint
import Submission.Lib.K4PolynomialNorming.OriginalEndpointSupport

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching

/-- A genuine six-switch experiment supplies a substantial family of the
constructed polynomial endpoints inside one enlargement of the ORIGINAL
counted physical support. Every sampled row carries both actual bases. -/
theorem actual_six_switch_polynomial_source {L Q C ι : Type*}
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
    (Tfield : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (point : L × ℝ → (Fin 3 → ℝ) × ℝ) (hpoint : Measurable point)
    (Target : Set ((Fin 3 → ℝ) × ℝ)) (hsupport : ∀ᵐ z ∂ν ⊗ₘ κ, point z ∈ Target)
    (I : Finset ι) (centers : ι → Fin 4 → ℝ) (widths : Fin 4 → ℝ)
    (η : Fin 4 → ℝ) (hηwidth : ∀ j, η j ≤ widths j)
    (hcover : ∀ y ∈ Target, ∃ i ∈ I, ∀ j,
      |(splitHeadCoordinates 3).symm y j-centers i j| ≤ widths j)
    (herror : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity (fun x =>
      causalRetentionWeights w₀
        (basisPencilRetention (fun z => control z.1) v r (Prod.fst ⁻¹' Long)) 6
          (Preorder.frestrictLe 6 x)),
      ∀ j, |(splitHeadCoordinates 3).symm
        (codedSixSwitchEndpoint Tfield (fun z => (point z).1) v
          (sixSwitchCoordinates control a h x)+point (x 0)) j-
            (splitHeadCoordinates 3).symm (point (x 6)) j| ≤ η j)
    (hpositive : (K*D)^6 * (μ.prod (Measure.pi (fun _ : Fin 6 => π))) univ * b +
      6 * ((ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ+p) < ((ν ⊗ₘ κ).withDensity w₀) univ) :
    ∃ Tplus : Set ((Fin 3 → ℝ) × ℝ), MeasurableSet Tplus ∧
      volume Tplus ≤ (I.card : ENNReal)*∏ j, ENNReal.ofReal (4*widths j) ∧
      ∃ row, ∃ A : Set (Fin 6 → ℝ), MeasurableSet A ∧ b < volume A ∧
        ∀ δ ∈ A, (row,splitHeadCoordinates 5 δ) ∈ sixSwitchCertificates Good v (r^3) U ∧
          codedSixSwitchEndpoint Tfield (fun z => (point z).1) v
            (row,splitHeadCoordinates 5 δ) + point row.1 ∈ Tplus := by
  let S := stateTimeSwitch ν κ state hstate
  letI := stateTimeSwitch_markov ν κ state hstate
  let w : (ℕ → L × ℝ) → ENNReal := fun x =>
    causalRetentionWeights w₀
      (basisPencilRetention (fun z => control z.1) v r (Prod.fst ⁻¹' Long)) 6
        (Preorder.frestrictLe 6 x)
  let start : (L × ℝ) × (Fin 6 → C) → (Fin 3 → ℝ) × ℝ := fun row => point row.1
  let endpoint := codedSixSwitchEndpoint Tfield (fun z => (point z).1) v
  obtain ⟨Tplus,hTplus,hvol,_htranslations,hae⟩ :=
    exists_original_rectangular_endpoint_support_of_coordinate_error 3 (ν ⊗ₘ κ) (fun _ => S)
      (fun _ => stateTimeSwitch_invariant ν κ state hstate) w 6 point Target hsupport
      I centers widths η hηwidth hcover (sixSwitchCoordinates control a h) start endpoint herror
  let F := {z | endpoint z+start z.1 ∈ Tplus}
  have hF : MeasurableSet F := codedSixSwitchEndpoint_target_measurable Tfield
    (fun z => (point z).1) (measurable_fst.comp hpoint) v start
    (hpoint.comp measurable_fst) Tplus hTplus
  obtain ⟨row,A,hA,hvolA,hcert⟩ := actual_substantial_six_basis_switch_family
    ν κ state hstate control hcontrol v r hr Long hLong Good hGood w₀ hw₀ hw₀1 hwGood
    μ π K D p b a h U hh hzero hrect htime hbroad ht hv F hF hae hpositive
  exact ⟨Tplus,hTplus,hvol,row,A,hA,hvolA,hcert⟩

end Submission.Lib.K4PolynomialNorming
