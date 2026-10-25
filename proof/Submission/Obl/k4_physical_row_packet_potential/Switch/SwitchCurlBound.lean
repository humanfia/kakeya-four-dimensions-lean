-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/SwitchCurlBound.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Curl coefficients of the interpolated field from the six-switch
experiment: the large-curl start mass bound of `SwitchCurlMass` is fed to
`Submission.Lib.K4PolynomialNorming.original_curl_coefficients_of_mass_budget`
(polynomial norming under the original base ceiling).
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.SwitchCurlMass
import Submission.Lib.K4PolynomialNorming.OriginalCurlSublevel
import Submission.Obl.k4_physical_row_packet_potential.Switch.BoxNorming

set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory ProbabilityTheory MvPolynomial
open scoped ProbabilityTheory ENNReal
open Submission.Lib.K4PolynomialNorming Submission.Lib.K4CubicTests
open Submission.Lib.K4ScalarActualSwitching Submission.Lib.K4ScalarSwitching

theorem curl_totalDegree_le (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (D : ℕ)
    (hT : ∀ i, (T i).totalDegree ≤ D) (i j : Fin 3) :
    (pderiv j (T i) - pderiv i (T j)).totalDegree ≤ D := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (Submission.Lib.K4PolynomialPotential.totalDegree_pderiv_le _ _).trans
      ((Nat.sub_le _ _).trans (hT i))
  · exact (Submission.Lib.K4PolynomialPotential.totalDegree_pderiv_le _ _).trans
      ((Nat.sub_le _ _).trans (hT j))

/-- The six-switch experiment bounds every curl coefficient of the field by
`Λ' ^ cCurl * θ`, provided the switching budget plus the base-ceiling
sublevel loss is below the full original mass. -/
theorem six_switch_curl_coefficients_le (D : ℕ) : ∃ cNorm cCurl : ℕ,
    ∀ {L Q C ι : Type*} [MeasurableSpace L] [MeasurableSpace Q] [MeasurableSpace C]
      [MeasurableSingletonClass Q] [Countable Q]
      [MeasurableSingletonClass C] [Countable C] [StandardBorelSpace C] [Nonempty C]
      [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
      (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
      [IsProbabilityMeasure (ν ⊗ₘ κ)]
      (state : L × ℝ → Q) (hstate : Measurable state)
      (control : L → C) (hcontrol : Measurable control)
      (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 < r)
      (Long : Set L) (hLong : MeasurableSet Long)
      (μ : Measure (L × ℝ)) [SFinite μ] (π : Measure C) [SigmaFinite π]
      (K Dt p : ENNReal) (a h U : ℝ) (hh : 0 < h) (hU : 0 < U)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (T i).totalDegree ≤ D)
      (point : L × ℝ → (Fin 3 → ℝ) × ℝ) (hpoint : Measurable point)
      (θ : ℝ) (hθ : 0 < θ)
      (hzero : (ν ⊗ₘ κ).withDensity
        ((largeFieldCurlStart T (fun z => (point z).1) θ).indicator 1) ≤ μ)
      (hrect : ∀ q (A : Set C), MeasurableSet A →
        (ν ⊗ₘ κ) {z | state z = q ∧ control z.1 ∈ A} ≤
          K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
      (htime : ∀ l ∈ Long, κ l ≤ ((ENNReal.ofReal h)⁻¹ * Dt) • (volume : Measure ℝ))
      (hbroad : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
        Module.finrank ℝ W < 3 →
          (conditionalResampling (ν ⊗ₘ κ) state hstate z).map (fun y => control y.1)
            {c | Metric.infDist (v c) (W : Set _) < r} ≤ p)
      (ht : ∀ᵐ z ∂ν ⊗ₘ κ, z.2 ∈ Icc a (a + h))
      (hv : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ j, |v (control z.1) j| ≤ U)
      (Target : Set ((Fin 3 → ℝ) × ℝ)) (hsupport : ∀ᵐ z ∂ν ⊗ₘ κ, point z ∈ Target)
      (I : Finset ι) (centers : ι → Fin 4 → ℝ) (widths : Fin 4 → ℝ)
      (η : Fin 4 → ℝ) (hηwidth : ∀ j, η j ≤ widths j)
      (hcover : ∀ y ∈ Target, ∃ i ∈ I, ∀ j,
        |(splitHeadCoordinates 3).symm y j - centers i j| ≤ widths j)
      (herror : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity
          (sixSwitchWeight ((largeFieldCurlStart T (fun z => (point z).1) θ).indicator 1)
            control v r Long),
        ∀ j, |(splitHeadCoordinates 3).symm
          (codedSixSwitchEndpoint T (fun z => (point z).1) v
            (sixSwitchCoordinates control a h x) + point (x 0)) j -
              (splitHeadCoordinates 3).symm (point (x 6)) j| ≤ η j)
      (Λ : ℝ) (hΛ : 2 ≤ Λ) (hwidth0 : 0 ≤ widths 0)
      (Kcap : ENNReal) (hcap : (ν ⊗ₘ κ).map (fun z => (point z).1) ≤ Kcap • volume)
      (hbox : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ j, |(point z).1 j| ≤ 1)
      (Λ' : ℝ) (hΛ' : 2 ≤ Λ')
      (hbudget : (K * Dt) ^ 6 * (μ.prod (Measure.pi (fun _ : Fin 6 => π))) univ *
            switchVolumeBound D cNorm I widths r U θ Λ +
          6 * ((ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ + p) + Kcap * ENNReal.ofReal Λ'⁻¹ < 1),
      ∀ i j m, |(pderiv j (T i) - pderiv i (T j)).coeff m| ≤ Λ' ^ cCurl * θ := by
  obtain ⟨cNorm, hmass⟩ := six_switch_large_curl_mass_le D
  obtain ⟨cCurl, hcurl⟩ := original_curl_coefficients_of_mass_budget D
  refine ⟨cNorm, cCurl, ?_⟩
  intro L Q C ι _ _ _ _ _ _ _ _ _ _ _ ν _ κ _ _ state hstate control hcontrol v r hr Long hLong
    μ _ π _ K Dt p a h U hh hU T hT point hpoint θ hθ hzero hrect htime hbroad ht hv
    Target hsupport I centers widths η hηwidth hcover herror Λ hΛ hwidth0 Kcap hcap hbox
    Λ' hΛ' hbudget
  have hupper := hmass ν κ state hstate control hcontrol v r hr Long hLong μ π K Dt p a h U hh hU
    T hT point hpoint θ hθ hzero hrect htime hbroad ht hv Target hsupport I centers widths η
    hηwidth hcover herror Λ hΛ hwidth0
  exact hcurl (ν ⊗ₘ κ) (fun z => (point z).1) (measurable_fst.comp hpoint) Kcap hcap hbox T
    (curl_totalDegree_le T D hT) Λ' θ hΛ' hθ.le 1
    ((K * Dt) ^ 6 * (μ.prod (Measure.pi (fun _ : Fin 6 => π))) univ *
            switchVolumeBound D cNorm I widths r U θ Λ +
          6 * ((ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ + p))
    (by rw [one_mul]; exact hupper) (by simpa only [one_mul] using hbudget)

/-- Radius-`R` version: the six-switch experiment bounds every curl coefficient of the field by
`Λ' ^ cCurl * θ`, provided the switching budget plus the base-ceiling
sublevel loss is below the full original mass. -/
theorem six_switch_curl_coefficients_le_box (D : ℕ) : ∃ cNorm cCurl : ℕ,
    ∀ {L Q C ι : Type*} [MeasurableSpace L] [MeasurableSpace Q] [MeasurableSpace C]
      [MeasurableSingletonClass Q] [Countable Q]
      [MeasurableSingletonClass C] [Countable C] [StandardBorelSpace C] [Nonempty C]
      [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
      (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
      [IsProbabilityMeasure (ν ⊗ₘ κ)]
      (state : L × ℝ → Q) (hstate : Measurable state)
      (control : L → C) (hcontrol : Measurable control)
      (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 < r)
      (Long : Set L) (hLong : MeasurableSet Long)
      (μ : Measure (L × ℝ)) [SFinite μ] (π : Measure C) [SigmaFinite π]
      (K Dt p : ENNReal) (a h U : ℝ) (hh : 0 < h) (hU : 0 < U)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (T i).totalDegree ≤ D)
      (point : L × ℝ → (Fin 3 → ℝ) × ℝ) (hpoint : Measurable point)
      (θ : ℝ) (hθ : 0 < θ)
      (hzero : (ν ⊗ₘ κ).withDensity
        ((largeFieldCurlStart T (fun z => (point z).1) θ).indicator 1) ≤ μ)
      (hrect : ∀ q (A : Set C), MeasurableSet A →
        (ν ⊗ₘ κ) {z | state z = q ∧ control z.1 ∈ A} ≤
          K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
      (htime : ∀ l ∈ Long, κ l ≤ ((ENNReal.ofReal h)⁻¹ * Dt) • (volume : Measure ℝ))
      (hbroad : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
        Module.finrank ℝ W < 3 →
          (conditionalResampling (ν ⊗ₘ κ) state hstate z).map (fun y => control y.1)
            {c | Metric.infDist (v c) (W : Set _) < r} ≤ p)
      (ht : ∀ᵐ z ∂ν ⊗ₘ κ, z.2 ∈ Icc a (a + h))
      (hv : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ j, |v (control z.1) j| ≤ U)
      (Target : Set ((Fin 3 → ℝ) × ℝ)) (hsupport : ∀ᵐ z ∂ν ⊗ₘ κ, point z ∈ Target)
      (I : Finset ι) (centers : ι → Fin 4 → ℝ) (widths : Fin 4 → ℝ)
      (η : Fin 4 → ℝ) (hηwidth : ∀ j, η j ≤ widths j)
      (hcover : ∀ y ∈ Target, ∃ i ∈ I, ∀ j,
        |(splitHeadCoordinates 3).symm y j - centers i j| ≤ widths j)
      (herror : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity
          (sixSwitchWeight ((largeFieldCurlStart T (fun z => (point z).1) θ).indicator 1)
            control v r Long),
        ∀ j, |(splitHeadCoordinates 3).symm
          (codedSixSwitchEndpoint T (fun z => (point z).1) v
            (sixSwitchCoordinates control a h x) + point (x 0)) j -
              (splitHeadCoordinates 3).symm (point (x 6)) j| ≤ η j)
      (Λ : ℝ) (hΛ : 2 ≤ Λ) (hwidth0 : 0 ≤ widths 0)
      (R : ℝ) (hR : 1 ≤ R)
      (Kcap : ENNReal)
      (hcap : (ν ⊗ₘ κ).map (fun z => fun j => R⁻¹ * (point z).1 j) ≤ Kcap • volume)
      (hbox : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ j, |(point z).1 j| ≤ R)
      (Λ' : ℝ) (hΛ' : 2 ≤ Λ')
      (hbudget : (K * Dt) ^ 6 * (μ.prod (Measure.pi (fun _ : Fin 6 => π))) univ *
            switchVolumeBound D cNorm I widths r U θ Λ +
          6 * ((ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ + p) + Kcap * ENNReal.ofReal Λ'⁻¹ < 1),
      ∀ i j m, |(pderiv j (T i) - pderiv i (T j)).coeff m| ≤ Λ' ^ cCurl * θ := by
  obtain ⟨cNorm, hmass⟩ := six_switch_large_curl_mass_le D
  obtain ⟨cCurl, hcurl⟩ := original_curl_coefficients_of_mass_budget_box D
  refine ⟨cNorm, cCurl, ?_⟩
  intro L Q C ι _ _ _ _ _ _ _ _ _ _ _ ν _ κ _ _ state hstate control hcontrol v r hr Long hLong
    μ _ π _ K Dt p a h U hh hU T hT point hpoint θ hθ hzero hrect htime hbroad ht hv
    Target hsupport I centers widths η hηwidth hcover herror Λ hΛ hwidth0 R hR Kcap hcap hbox
    Λ' hΛ' hbudget
  have hupper := hmass ν κ state hstate control hcontrol v r hr Long hLong μ π K Dt p a h U hh hU
    T hT point hpoint θ hθ hzero hrect htime hbroad ht hv Target hsupport I centers widths η
    hηwidth hcover herror Λ hΛ hwidth0
  exact hcurl (ν ⊗ₘ κ) (fun z => (point z).1) (measurable_fst.comp hpoint) R hR Kcap hcap hbox T
    (curl_totalDegree_le T D hT) Λ' θ hΛ' hθ.le 1
    ((K * Dt) ^ 6 * (μ.prod (Measure.pi (fun _ : Fin 6 => π))) univ *
            switchVolumeBound D cNorm I widths r U θ Λ +
          6 * ((ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ + p))
    (by rw [one_mul]; exact hupper) (by simpa only [one_mul] using hbudget)

end Submission.Obl.k4_physical_row_packet_potential.Switch
