-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/FieldExperiment.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). The six-switch conservativity on one packet, from a field
certificate stated for the unnormalized source law
`μ = (ν₀ × τ).withDensity F` with `F ≤ 1`.

The source law is normalized once and disintegrated
(`normalized_original_incidence_disintegration`); long lines are those of
duration at least `q`; the endpoint simulation error comes from incidence
point fits and shared-state geometry
(`actual_quadratic_six_switch_endpoint_error_of_original_point_fit_ae`);
then `six_switch_curl_coefficients_le` bounds the curl coefficients.
All lemmas used from `Submission.Lib.K4PolynomialNorming` are by session x0001.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.SwitchCurlBound
import Submission.Obl.k4_physical_row_packet_potential.Switch.ResamplingRatio
import Submission.Obl.k4_physical_row_packet_potential.Switch.RetainedLong
import Submission.Lib.K4PolynomialNorming.NormalizedOriginalIncidence
import Submission.Lib.K4PolynomialNorming.ActualQuadraticPointFitSimulation

set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory ProbabilityTheory MvPolynomial
open scoped ProbabilityTheory ENNReal
open Submission.Lib.K4PolynomialNorming Submission.Lib.K4CubicTests
open Submission.Lib.K4ScalarActualSwitching Submission.Lib.K4ScalarSwitching

/-- The simulated height error of the six-leg path. -/
noncomputable def simHeightError (D : ℕ) (Ktime ε ηs τv ζ B U A : ℝ) : ℝ :=
  6 * (ζ + ((8 * ((D : ℝ) + 2) * Ktime) ^ (D + 1) * ε) + (3 * B) * τv +
    (3 * U * A) * (ηs + τv) + (3 * U * A) * (6 * (ηs + τv)))

theorem smul_measure_mono {α : Type*} [MeasurableSpace α] (c : ENNReal) {μ ν : Measure α}
    (h : μ ≤ ν) : c • μ ≤ c • ν := by
  rw [Measure.le_iff'] at h ⊢
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (h s) c

/-- Six-switch conservativity on one packet from an unnormalized field
certificate. -/
theorem field_six_switch_curl_coefficients (D : ℕ) : ∃ cNorm cCurl : ℕ,
    ∀ {L Q C ι : Type*} [MeasurableSpace L] [MeasurableSingletonClass L]
      [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q] [StandardBorelSpace Q]
      [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C] [StandardBorelSpace C]
      [Nonempty C] [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
      (ν₀ : Measure L) [IsFiniteMeasure ν₀] (τ : Measure ℝ) [IsProbabilityMeasure τ]
      (hτ : τ ≤ volume)
      (F : L × ℝ → ENNReal) (hF : Measurable F) (hF1 : ∀ z, F z ≤ 1)
      (hpos : 0 < ((ν₀.prod τ).withDensity F) univ)
      (state : L × ℝ → Q) (hstate : Measurable state)
      (control : L → C) (hcontrol : Measurable control) (v : C → EuclideanSpace ℝ (Fin 3))
      (π : Measure C) [IsProbabilityMeasure π]
      (K p : ENNReal) (r U : ℝ) (hr : 0 < r) (hU : 0 < U)
      (hrect : ∀ q (A : Set C), MeasurableSet A →
        ((ν₀.prod τ).withDensity F) {z | state z = q ∧ control z.1 ∈ A} ≤
          K * ((ν₀.prod τ).withDensity F) (state ⁻¹' {q}) * π A)
      (hratio : ∀ q (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ W < 3 →
        ((ν₀.prod τ).withDensity F)
            (state ⁻¹' {q} ∩ {z | Metric.infDist (v (control z.1)) (W : Set _) < r}) ≤
          p * ((ν₀.prod τ).withDensity F) (state ⁻¹' {q}))
      (a h : ℝ) (hh : 0 < h)
      (ht : ∀ᵐ z ∂((ν₀.prod τ).withDensity F), z.2 ∈ Icc a (a + h))
      (hv : ∀ᵐ z ∂((ν₀.prod τ).withDensity F), ∀ j, |v (control z.1) j| ≤ U)
      (base velocity : L → Fin 3 → ℝ) (height₀ height₁ height₂ : L → ℝ)
      (hb : Measurable base) (hu : Measurable velocity)
      (hz₀ : Measurable height₀) (hz₁ : Measurable height₁) (hz₂ : Measurable height₂)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (T i).totalDegree ≤ D)
      (q : ℝ) (hq : 0 < q) (hqh : q ≤ h)
      (ε ηs τv ζ B A R : ℝ) (hε : 0 ≤ ε) (hηs : 0 ≤ ηs) (hτv : 0 ≤ τv) (hζ : 0 ≤ ζ)
      (hB : 0 ≤ B) (hA : 0 ≤ A)
      (hvelocity : ∀ᵐ z ∂((ν₀.prod τ).withDensity F),
        ‖velocity z.1 - (fun j : Fin 3 => v (control z.1) j)‖ ≤ τv)
      (hfit : ∀ᵐ z ∂((ν₀.prod τ).withDensity F),
        |quadraticHeightSpeed (height₁ z.1) (height₂ z.1) ((z.2 - a) / h) - ∑ j,
          velocity z.1 j * MvPolynomial.eval
            (base z.1 + ((z.2 - a) / h) • velocity z.1) (T j)| ≤ ε)
      (hconf : ∀ᵐ z ∂((ν₀.prod τ).withDensity F),
        z.1 ∈ Submission.Lib.K4Homogenization.durationRetained τ F univ (ENNReal.ofReal q) →
          ∀ t ∈ Icc (0 : ℝ) 1, ‖base z.1 + t • velocity z.1‖ ≤ R)
      (hfield : ∀ x ∈ Metric.closedBall 0 (R + 7 * (ηs + τv)), ∀ j,
        |MvPolynomial.eval x (T j)| ≤ B)
      (hspace : ∀ x ∈ Metric.closedBall 0 (R + 7 * (ηs + τv)),
        ∀ y ∈ Metric.closedBall 0 (R + 7 * (ηs + τv)), ∀ j,
          |MvPolynomial.eval x (T j) - MvPolynomial.eval y (T j)| ≤ A * ‖x - y‖)
      (Valid : L × ℝ → Prop) (hValid : ∀ᵐ z ∂((ν₀.prod τ).withDensity F), Valid z)
      (hshared : ∀ old redraw, state redraw = state old → Valid old → Valid redraw →
        (old.2 - a) / h ∈ Icc (0 : ℝ) 1 →
        redraw.1 ∈ Submission.Lib.K4Homogenization.durationRetained τ F univ (ENNReal.ofReal q) →
        ‖(quadraticLinePoint base velocity height₀ height₁ height₂ redraw.1 ((old.2 - a) / h)).1 -
          (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ old).1‖ ≤ ηs ∧
        |(quadraticLinePoint base velocity height₀ height₁ height₂ redraw.1 ((old.2 - a) / h)).2 -
          (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ old).2| ≤ ζ)
      (Target : Set ((Fin 3 → ℝ) × ℝ))
      (hsupport : ∀ᵐ z ∂((ν₀.prod τ).withDensity F),
        quadraticIncidencePoint a h base velocity height₀ height₁ height₂ z ∈ Target)
      (I : Finset ι) (centers : ι → Fin 4 → ℝ) (widths : Fin 4 → ℝ)
      (hcover : ∀ y ∈ Target, ∃ i ∈ I, ∀ j,
        |(splitHeadCoordinates 3).symm y j - centers i j| ≤ widths j)
      (hwidthH : simHeightError D (h / q) ε ηs τv ζ B U A ≤ widths 0)
      (hwidthB : ∀ k : Fin 3, 6 * (ηs + τv) ≤ widths k.succ)
      (Kcap : ENNReal)
      (hcap : ((ν₀.prod τ).withDensity F).map
          (fun z => (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ z).1) ≤
        Kcap • volume)
      (hbox : ∀ᵐ z ∂((ν₀.prod τ).withDensity F), ∀ j,
        |(quadraticIncidencePoint a h base velocity height₀ height₁ height₂ z).1 j| ≤ 1)
      (θ Λ Λ' : ℝ) (hθ : 0 < θ) (hΛ : 2 ≤ Λ) (hΛ' : 2 ≤ Λ')
      (hbudget : (K * ENNReal.ofReal (h / q)) ^ 6 *
            switchVolumeBound D cNorm I widths r U θ Λ +
          6 * ((((ν₀.prod τ).withDensity F) univ)⁻¹ * (ENNReal.ofReal q * ν₀ univ) + p) +
          (((ν₀.prod τ).withDensity F) univ)⁻¹ * Kcap * ENNReal.ofReal Λ'⁻¹ < 1),
      ∀ i j m, |(pderiv j (T i) - pderiv i (T j)).coeff m| ≤ Λ' ^ cCurl * θ := by
  obtain ⟨cNorm, cCurl, hcurl⟩ := six_switch_curl_coefficients_le D
  refine ⟨cNorm, cCurl, ?_⟩
  intro L Q C ι _ _ _ _ _ _ _ _ _ _ _ _ _ ν₀ _ τ _ hτ F hF hF1 hpos state hstate control hcontrol
    v π _ K p r U hr hU hrect hratio a h hh ht hv base velocity height₀ height₁ height₂
    hb hu hz₀ hz₁ hz₂ T hT q hq hqh ε ηs τv ζ B A R hε hηs hτv hζ hB hA hvelocity hfit hconf
    hfield hspace Valid hValid hshared Target hsupport I centers widths hcover hwidthH hwidthB
    Kcap hcap hbox θ Λ Λ' hθ hΛ hΛ' hbudget
  set μ := (ν₀.prod τ).withDensity F with hμ
  obtain ⟨hP, ν, hν, κ, hκ, hjoint, hlong, hshort⟩ :=
    normalized_original_incidence_disintegration ν₀ τ F hF 1 ENNReal.one_ne_top hF1 hpos
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    calc μ univ ≤ (1 : ENNReal) * (ν₀.prod τ) univ := by
          rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
          exact (lintegral_mono hF1).trans (by simp)
      _ < ⊤ := by simp
  have : IsProbabilityMeasure ((μ univ)⁻¹ • μ) := hP
  have : IsProbabilityMeasure ν := hν
  have : IsMarkovKernel κ := hκ
  have hPμ : ν ⊗ₘ κ = (μ univ)⁻¹ • μ := hjoint
  have : IsProbabilityMeasure (ν ⊗ₘ κ) := by rw [hPμ]; exact hP
  set c : ENNReal := (μ univ)⁻¹ with hc
  -- a.e. statements and caps transfer to the normalized law
  have hae {p : L × ℝ → Prop} (h : ∀ᵐ z ∂μ, p z) : ∀ᵐ z ∂(ν ⊗ₘ κ), p z := by
    rw [hPμ]; exact Measure.ae_smul_measure h _
  have happly (s : Set (L × ℝ)) : (ν ⊗ₘ κ) s = c * μ s := by
    rw [hPμ, Measure.smul_apply, smul_eq_mul]
  set Long := Submission.Lib.K4Homogenization.durationRetained τ F univ (ENNReal.ofReal q)
    with hLongDef
  have hLong : MeasurableSet Long :=
    Submission.Lib.K4Homogenization.measurableSet_durationRetained τ hF univ _
  have hqpos : 0 < ENNReal.ofReal q := ENNReal.ofReal_pos.mpr hq
  have hhpos : 0 < ENNReal.ofReal h := ENNReal.ofReal_pos.mpr hh
  have hrate : (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal (h / q) = 1 / ENNReal.ofReal q := by
    rw [ENNReal.ofReal_div_of_pos hq, div_eq_mul_inv, ← mul_assoc,
      ENNReal.inv_mul_cancel hhpos.ne' ENNReal.ofReal_ne_top, one_mul, one_div]
  have htime : ∀ l ∈ Long,
      κ l ≤ ((ENNReal.ofReal h)⁻¹ * ENNReal.ofReal (h / q)) • (volume : Measure ℝ) := by
    intro l hl
    rw [hrate]
    exact (hlong (ENNReal.ofReal q) hqpos l hl).trans (smul_measure_mono _ hτ)
  have hpoint : Measurable (quadraticIncidencePoint a h base velocity height₀ height₁ height₂) :=
    quadraticIncidencePoint_measurable a h base velocity height₀ height₁ height₂
      hb hu hz₀ hz₁ hz₂
  -- the simulated endpoint error
  set point := quadraticIncidencePoint a h base velocity height₀ height₁ height₂
  set wLarge : L × ℝ → ENNReal :=
    (largeFieldCurlStart T (fun z => (point z).1) θ).indicator 1 with hwLarge
  have hwLargem : Measurable wLarge := measurable_one.indicator
    (largeFieldCurlStart_measurable T _ (measurable_fst.comp hpoint) θ)
  have hretained := ae_retained_long (actualSwitchedPathMeasure ν κ state hstate) wLarge hwLargem
    (fun z : L × ℝ => control z.1) (hcontrol.comp measurable_fst) v r (Prod.fst ⁻¹' Long)
    (hLong.preimage measurable_fst)
  have hsim := actual_quadratic_six_switch_endpoint_error_of_original_point_fit_ae ν κ state hstate
    control v a h hh Long hLong base velocity height₀ height₁ height₂ hb hu hz₀ hz₁ hz₂ T D hT
    (h / q) ((one_le_div hq).mpr hqh) (by simpa only [hrate] using htime)
    ε ηs τv ζ B U A R hε hηs hτv hB hU.le hA (hae ht) (hae hvelocity) (hae hv) (hae hfit)
    (hae hconf) hfield hspace Valid (hae hValid) hshared (sixSwitchWeight wLarge control v r Long)
    (hretained.mono (fun x hx k hk => hx k hk))
  have herror : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity
      (sixSwitchWeight wLarge control v r Long),
      ∀ j, |(splitHeadCoordinates 3).symm
        (codedSixSwitchEndpoint T (fun z => (point z).1) v
          (sixSwitchCoordinates control a h x) + point (x 0)) j -
            (splitHeadCoordinates 3).symm (point (x 6)) j| ≤
        (Fin.cons (simHeightError D (h / q) ε ηs τv ζ B U A)
          (fun _ : Fin 3 => 6 * (ηs + τv)) : Fin 4 → ℝ) j := by
    filter_upwards [hsim] with x hx
    obtain ⟨hxb, hxh, _⟩ := hx
    apply splitHeadCoordinates_error_of_base_height 3
    · simpa only [Prod.fst_add] using hxb
    · simpa only [Prod.snd_add, simHeightError] using hxh
  have hηwidth : ∀ j, (Fin.cons (simHeightError D (h / q) ε ηs τv ζ B U A)
      (fun _ : Fin 3 => 6 * (ηs + τv)) : Fin 4 → ℝ) j ≤ widths j := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [Fin.cons_zero] using hwidthH
    · simpa only [Fin.cons_succ] using hwidthB k
  have hsimpos : 0 ≤ simHeightError D (h / q) ε ηs τv ζ B U A := by
    unfold simHeightError
    have : 0 < h / q := div_pos hh hq
    positivity
  have hwidth0 : 0 ≤ widths 0 := hsimpos.trans hwidthH
  -- normalized caps
  have hrectP : ∀ q (A : Set C), MeasurableSet A →
      (ν ⊗ₘ κ) {z | state z = q ∧ control z.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A := by
    intro q A hA
    rw [happly, happly]
    calc c * μ {z | state z = q ∧ control z.1 ∈ A}
        ≤ c * (K * μ (state ⁻¹' {q}) * π A) := mul_le_mul_right (hrect q A hA) _
      _ = K * (c * μ (state ⁻¹' {q})) * π A := by ring
  have hratioP : ∀ q (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ W < 3 →
      (ν ⊗ₘ κ) (state ⁻¹' {q} ∩ {z | Metric.infDist (v (control z.1)) (W : Set _) < r}) ≤
        p * (ν ⊗ₘ κ) (state ⁻¹' {q}) := by
    intro q W hW
    rw [happly, happly]
    calc c * μ (state ⁻¹' {q} ∩ {z | Metric.infDist (v (control z.1)) (W : Set _) < r})
        ≤ c * (p * μ (state ⁻¹' {q})) := mul_le_mul_right (hratio q W hW) _
      _ = p * (c * μ (state ⁻¹' {q})) := by ring
  have hbroad := broad_resampling_of_state_ratio (ν ⊗ₘ κ) state hstate control hcontrol v r p hratioP
  have hzero : (ν ⊗ₘ κ).withDensity wLarge ≤ ν ⊗ₘ κ := by
    calc (ν ⊗ₘ κ).withDensity wLarge ≤ (ν ⊗ₘ κ).withDensity 1 := by
          apply withDensity_mono
          exact Filter.Eventually.of_forall (fun z => by
            by_cases hz : z ∈ largeFieldCurlStart T (fun z => (point z).1) θ
            · simp [wLarge, hz]
            · simp [wLarge, hz])
      _ = ν ⊗ₘ κ := withDensity_one
  have hcapP : (ν ⊗ₘ κ).map (fun z => (point z).1) ≤ (c * Kcap) • volume := by
    have hm : AEMeasurable (fun z => (point z).1) μ :=
      (measurable_fst.comp hpoint).aemeasurable
    rw [hPμ, Measure.map_smul, mul_smul]
    · exact smul_measure_mono _ hcap
    · exact hm
  have hprodone : ((ν ⊗ₘ κ).prod (Measure.pi (fun _ : Fin 6 => π))) univ = 1 := by
    rw [← univ_prod_univ, Measure.prod_prod, measure_univ, measure_univ, one_mul]
  have hshortP : (ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ ≤ c * (ENNReal.ofReal q * ν₀ univ) := by
    rw [hPμ]
    exact hshort (ENNReal.ofReal q)
  have hbudgetP : (K * ENNReal.ofReal (h / q)) ^ 6 *
        ((ν ⊗ₘ κ).prod (Measure.pi (fun _ : Fin 6 => π))) univ *
          switchVolumeBound D cNorm I widths r U θ Λ +
        6 * ((ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ + p) + (c * Kcap) * ENNReal.ofReal Λ'⁻¹ < 1 := by
    rw [hprodone, mul_one]
    refine lt_of_le_of_lt ?_ hbudget
    gcongr
  exact hcurl ν κ state hstate control hcontrol v r hr Long hLong (ν ⊗ₘ κ) π K
    (ENNReal.ofReal (h / q)) p a h U hh hU T hT point hpoint θ hθ hzero hrectP htime hbroad
    (hae ht) (hae hv) Target (hae hsupport) I centers widths _ hηwidth hcover herror Λ hΛ
    hwidth0 (c * Kcap) hcapP (hae hbox) Λ' hΛ' hbudgetP

/-- Radius-`R` version of `field_six_switch_curl_coefficients`: the base
points lie in a box of radius `R ≥ 1`, with the ceiling stated after
rescaling to the unit box. -/
theorem field_six_switch_curl_coefficients_box (D : ℕ) : ∃ cNorm cCurl : ℕ,
    ∀ {L Q C ι : Type*} [MeasurableSpace L] [MeasurableSingletonClass L]
      [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q] [StandardBorelSpace Q]
      [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C] [StandardBorelSpace C]
      [Nonempty C] [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
      (ν₀ : Measure L) [IsFiniteMeasure ν₀] (τ : Measure ℝ) [IsProbabilityMeasure τ]
      (hτ : τ ≤ volume)
      (F : L × ℝ → ENNReal) (hF : Measurable F) (hF1 : ∀ z, F z ≤ 1)
      (hpos : 0 < ((ν₀.prod τ).withDensity F) univ)
      (state : L × ℝ → Q) (hstate : Measurable state)
      (control : L → C) (hcontrol : Measurable control) (v : C → EuclideanSpace ℝ (Fin 3))
      (π : Measure C) [IsProbabilityMeasure π]
      (K p : ENNReal) (r U : ℝ) (hr : 0 < r) (hU : 0 < U)
      (hrect : ∀ q (A : Set C), MeasurableSet A →
        ((ν₀.prod τ).withDensity F) {z | state z = q ∧ control z.1 ∈ A} ≤
          K * ((ν₀.prod τ).withDensity F) (state ⁻¹' {q}) * π A)
      (hratio : ∀ q (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ W < 3 →
        ((ν₀.prod τ).withDensity F)
            (state ⁻¹' {q} ∩ {z | Metric.infDist (v (control z.1)) (W : Set _) < r}) ≤
          p * ((ν₀.prod τ).withDensity F) (state ⁻¹' {q}))
      (a h : ℝ) (hh : 0 < h)
      (ht : ∀ᵐ z ∂((ν₀.prod τ).withDensity F), z.2 ∈ Icc a (a + h))
      (hv : ∀ᵐ z ∂((ν₀.prod τ).withDensity F), ∀ j, |v (control z.1) j| ≤ U)
      (base velocity : L → Fin 3 → ℝ) (height₀ height₁ height₂ : L → ℝ)
      (hb : Measurable base) (hu : Measurable velocity)
      (hz₀ : Measurable height₀) (hz₁ : Measurable height₁) (hz₂ : Measurable height₂)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (T i).totalDegree ≤ D)
      (q : ℝ) (hq : 0 < q) (hqh : q ≤ h)
      (ε ηs τv ζ B A R : ℝ) (hε : 0 ≤ ε) (hηs : 0 ≤ ηs) (hτv : 0 ≤ τv) (hζ : 0 ≤ ζ)
      (hB : 0 ≤ B) (hA : 0 ≤ A)
      (hvelocity : ∀ᵐ z ∂((ν₀.prod τ).withDensity F),
        ‖velocity z.1 - (fun j : Fin 3 => v (control z.1) j)‖ ≤ τv)
      (hfit : ∀ᵐ z ∂((ν₀.prod τ).withDensity F),
        |quadraticHeightSpeed (height₁ z.1) (height₂ z.1) ((z.2 - a) / h) - ∑ j,
          velocity z.1 j * MvPolynomial.eval
            (base z.1 + ((z.2 - a) / h) • velocity z.1) (T j)| ≤ ε)
      (hconf : ∀ᵐ z ∂((ν₀.prod τ).withDensity F),
        z.1 ∈ Submission.Lib.K4Homogenization.durationRetained τ F univ (ENNReal.ofReal q) →
          ∀ t ∈ Icc (0 : ℝ) 1, ‖base z.1 + t • velocity z.1‖ ≤ R)
      (hfield : ∀ x ∈ Metric.closedBall 0 (R + 7 * (ηs + τv)), ∀ j,
        |MvPolynomial.eval x (T j)| ≤ B)
      (hspace : ∀ x ∈ Metric.closedBall 0 (R + 7 * (ηs + τv)),
        ∀ y ∈ Metric.closedBall 0 (R + 7 * (ηs + τv)), ∀ j,
          |MvPolynomial.eval x (T j) - MvPolynomial.eval y (T j)| ≤ A * ‖x - y‖)
      (Valid : L × ℝ → Prop) (hValid : ∀ᵐ z ∂((ν₀.prod τ).withDensity F), Valid z)
      (hshared : ∀ old redraw, state redraw = state old → Valid old → Valid redraw →
        (old.2 - a) / h ∈ Icc (0 : ℝ) 1 →
        redraw.1 ∈ Submission.Lib.K4Homogenization.durationRetained τ F univ (ENNReal.ofReal q) →
        ‖(quadraticLinePoint base velocity height₀ height₁ height₂ redraw.1 ((old.2 - a) / h)).1 -
          (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ old).1‖ ≤ ηs ∧
        |(quadraticLinePoint base velocity height₀ height₁ height₂ redraw.1 ((old.2 - a) / h)).2 -
          (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ old).2| ≤ ζ)
      (Target : Set ((Fin 3 → ℝ) × ℝ))
      (hsupport : ∀ᵐ z ∂((ν₀.prod τ).withDensity F),
        quadraticIncidencePoint a h base velocity height₀ height₁ height₂ z ∈ Target)
      (I : Finset ι) (centers : ι → Fin 4 → ℝ) (widths : Fin 4 → ℝ)
      (hcover : ∀ y ∈ Target, ∃ i ∈ I, ∀ j,
        |(splitHeadCoordinates 3).symm y j - centers i j| ≤ widths j)
      (hwidthH : simHeightError D (h / q) ε ηs τv ζ B U A ≤ widths 0)
      (hwidthB : ∀ k : Fin 3, 6 * (ηs + τv) ≤ widths k.succ)
      (Rb : ℝ) (hRb : 1 ≤ Rb) (Kcap : ENNReal)
      (hcap : ((ν₀.prod τ).withDensity F).map
          (fun z => fun j => Rb⁻¹ *
            (quadraticIncidencePoint a h base velocity height₀ height₁ height₂ z).1 j) ≤
        Kcap • volume)
      (hbox : ∀ᵐ z ∂((ν₀.prod τ).withDensity F), ∀ j,
        |(quadraticIncidencePoint a h base velocity height₀ height₁ height₂ z).1 j| ≤ Rb)
      (θ Λ Λ' : ℝ) (hθ : 0 < θ) (hΛ : 2 ≤ Λ) (hΛ' : 2 ≤ Λ')
      (hbudget : (K * ENNReal.ofReal (h / q)) ^ 6 *
            switchVolumeBound D cNorm I widths r U θ Λ +
          6 * ((((ν₀.prod τ).withDensity F) univ)⁻¹ * (ENNReal.ofReal q * ν₀ univ) + p) +
          (((ν₀.prod τ).withDensity F) univ)⁻¹ * Kcap * ENNReal.ofReal Λ'⁻¹ < 1),
      ∀ i j m, |(pderiv j (T i) - pderiv i (T j)).coeff m| ≤ Λ' ^ cCurl * θ := by
  obtain ⟨cNorm, cCurl, hcurl⟩ := six_switch_curl_coefficients_le_box D
  refine ⟨cNorm, cCurl, ?_⟩
  intro L Q C ι _ _ _ _ _ _ _ _ _ _ _ _ _ ν₀ _ τ _ hτ F hF hF1 hpos state hstate control hcontrol
    v π _ K p r U hr hU hrect hratio a h hh ht hv base velocity height₀ height₁ height₂
    hb hu hz₀ hz₁ hz₂ T hT q hq hqh ε ηs τv ζ B A R hε hηs hτv hζ hB hA hvelocity hfit hconf
    hfield hspace Valid hValid hshared Target hsupport I centers widths hcover hwidthH hwidthB
    Rb hRb Kcap hcap hbox θ Λ Λ' hθ hΛ hΛ' hbudget
  set μ := (ν₀.prod τ).withDensity F with hμ
  obtain ⟨hP, ν, hν, κ, hκ, hjoint, hlong, hshort⟩ :=
    normalized_original_incidence_disintegration ν₀ τ F hF 1 ENNReal.one_ne_top hF1 hpos
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    calc μ univ ≤ (1 : ENNReal) * (ν₀.prod τ) univ := by
          rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
          exact (lintegral_mono hF1).trans (by simp)
      _ < ⊤ := by simp
  have : IsProbabilityMeasure ((μ univ)⁻¹ • μ) := hP
  have : IsProbabilityMeasure ν := hν
  have : IsMarkovKernel κ := hκ
  have hPμ : ν ⊗ₘ κ = (μ univ)⁻¹ • μ := hjoint
  have : IsProbabilityMeasure (ν ⊗ₘ κ) := by rw [hPμ]; exact hP
  set c : ENNReal := (μ univ)⁻¹ with hc
  -- a.e. statements and caps transfer to the normalized law
  have hae {p : L × ℝ → Prop} (h : ∀ᵐ z ∂μ, p z) : ∀ᵐ z ∂(ν ⊗ₘ κ), p z := by
    rw [hPμ]; exact Measure.ae_smul_measure h _
  have happly (s : Set (L × ℝ)) : (ν ⊗ₘ κ) s = c * μ s := by
    rw [hPμ, Measure.smul_apply, smul_eq_mul]
  set Long := Submission.Lib.K4Homogenization.durationRetained τ F univ (ENNReal.ofReal q)
    with hLongDef
  have hLong : MeasurableSet Long :=
    Submission.Lib.K4Homogenization.measurableSet_durationRetained τ hF univ _
  have hqpos : 0 < ENNReal.ofReal q := ENNReal.ofReal_pos.mpr hq
  have hhpos : 0 < ENNReal.ofReal h := ENNReal.ofReal_pos.mpr hh
  have hrate : (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal (h / q) = 1 / ENNReal.ofReal q := by
    rw [ENNReal.ofReal_div_of_pos hq, div_eq_mul_inv, ← mul_assoc,
      ENNReal.inv_mul_cancel hhpos.ne' ENNReal.ofReal_ne_top, one_mul, one_div]
  have htime : ∀ l ∈ Long,
      κ l ≤ ((ENNReal.ofReal h)⁻¹ * ENNReal.ofReal (h / q)) • (volume : Measure ℝ) := by
    intro l hl
    rw [hrate]
    exact (hlong (ENNReal.ofReal q) hqpos l hl).trans (smul_measure_mono _ hτ)
  have hpoint : Measurable (quadraticIncidencePoint a h base velocity height₀ height₁ height₂) :=
    quadraticIncidencePoint_measurable a h base velocity height₀ height₁ height₂
      hb hu hz₀ hz₁ hz₂
  -- the simulated endpoint error
  set point := quadraticIncidencePoint a h base velocity height₀ height₁ height₂
  set wLarge : L × ℝ → ENNReal :=
    (largeFieldCurlStart T (fun z => (point z).1) θ).indicator 1 with hwLarge
  have hwLargem : Measurable wLarge := measurable_one.indicator
    (largeFieldCurlStart_measurable T _ (measurable_fst.comp hpoint) θ)
  have hretained := ae_retained_long (actualSwitchedPathMeasure ν κ state hstate) wLarge hwLargem
    (fun z : L × ℝ => control z.1) (hcontrol.comp measurable_fst) v r (Prod.fst ⁻¹' Long)
    (hLong.preimage measurable_fst)
  have hsim := actual_quadratic_six_switch_endpoint_error_of_original_point_fit_ae ν κ state hstate
    control v a h hh Long hLong base velocity height₀ height₁ height₂ hb hu hz₀ hz₁ hz₂ T D hT
    (h / q) ((one_le_div hq).mpr hqh) (by simpa only [hrate] using htime)
    ε ηs τv ζ B U A R hε hηs hτv hB hU.le hA (hae ht) (hae hvelocity) (hae hv) (hae hfit)
    (hae hconf) hfield hspace Valid (hae hValid) hshared (sixSwitchWeight wLarge control v r Long)
    (hretained.mono (fun x hx k hk => hx k hk))
  have herror : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity
      (sixSwitchWeight wLarge control v r Long),
      ∀ j, |(splitHeadCoordinates 3).symm
        (codedSixSwitchEndpoint T (fun z => (point z).1) v
          (sixSwitchCoordinates control a h x) + point (x 0)) j -
            (splitHeadCoordinates 3).symm (point (x 6)) j| ≤
        (Fin.cons (simHeightError D (h / q) ε ηs τv ζ B U A)
          (fun _ : Fin 3 => 6 * (ηs + τv)) : Fin 4 → ℝ) j := by
    filter_upwards [hsim] with x hx
    obtain ⟨hxb, hxh, _⟩ := hx
    apply splitHeadCoordinates_error_of_base_height 3
    · simpa only [Prod.fst_add] using hxb
    · simpa only [Prod.snd_add, simHeightError] using hxh
  have hηwidth : ∀ j, (Fin.cons (simHeightError D (h / q) ε ηs τv ζ B U A)
      (fun _ : Fin 3 => 6 * (ηs + τv)) : Fin 4 → ℝ) j ≤ widths j := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [Fin.cons_zero] using hwidthH
    · simpa only [Fin.cons_succ] using hwidthB k
  have hsimpos : 0 ≤ simHeightError D (h / q) ε ηs τv ζ B U A := by
    unfold simHeightError
    have : 0 < h / q := div_pos hh hq
    positivity
  have hwidth0 : 0 ≤ widths 0 := hsimpos.trans hwidthH
  -- normalized caps
  have hrectP : ∀ q (A : Set C), MeasurableSet A →
      (ν ⊗ₘ κ) {z | state z = q ∧ control z.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A := by
    intro q A hA
    rw [happly, happly]
    calc c * μ {z | state z = q ∧ control z.1 ∈ A}
        ≤ c * (K * μ (state ⁻¹' {q}) * π A) := mul_le_mul_right (hrect q A hA) _
      _ = K * (c * μ (state ⁻¹' {q})) * π A := by ring
  have hratioP : ∀ q (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ W < 3 →
      (ν ⊗ₘ κ) (state ⁻¹' {q} ∩ {z | Metric.infDist (v (control z.1)) (W : Set _) < r}) ≤
        p * (ν ⊗ₘ κ) (state ⁻¹' {q}) := by
    intro q W hW
    rw [happly, happly]
    calc c * μ (state ⁻¹' {q} ∩ {z | Metric.infDist (v (control z.1)) (W : Set _) < r})
        ≤ c * (p * μ (state ⁻¹' {q})) := mul_le_mul_right (hratio q W hW) _
      _ = p * (c * μ (state ⁻¹' {q})) := by ring
  have hbroad := broad_resampling_of_state_ratio (ν ⊗ₘ κ) state hstate control hcontrol v r p hratioP
  have hzero : (ν ⊗ₘ κ).withDensity wLarge ≤ ν ⊗ₘ κ := by
    calc (ν ⊗ₘ κ).withDensity wLarge ≤ (ν ⊗ₘ κ).withDensity 1 := by
          apply withDensity_mono
          exact Filter.Eventually.of_forall (fun z => by
            by_cases hz : z ∈ largeFieldCurlStart T (fun z => (point z).1) θ
            · simp [wLarge, hz]
            · simp [wLarge, hz])
      _ = ν ⊗ₘ κ := withDensity_one
  have hcapP : (ν ⊗ₘ κ).map (fun z => fun j => Rb⁻¹ * (point z).1 j) ≤ (c * Kcap) • volume := by
    have hm : AEMeasurable (fun z => fun j => Rb⁻¹ * (point z).1 j) μ := by
      apply Measurable.aemeasurable
      apply measurable_pi_iff.mpr
      intro j
      exact ((measurable_pi_apply j).comp (measurable_fst.comp hpoint)).const_mul _
    rw [hPμ, Measure.map_smul, mul_smul]
    · exact smul_measure_mono _ hcap
    · exact hm
  have hprodone : ((ν ⊗ₘ κ).prod (Measure.pi (fun _ : Fin 6 => π))) univ = 1 := by
    rw [← univ_prod_univ, Measure.prod_prod, measure_univ, measure_univ, one_mul]
  have hshortP : (ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ ≤ c * (ENNReal.ofReal q * ν₀ univ) := by
    rw [hPμ]
    exact hshort (ENNReal.ofReal q)
  have hbudgetP : (K * ENNReal.ofReal (h / q)) ^ 6 *
        ((ν ⊗ₘ κ).prod (Measure.pi (fun _ : Fin 6 => π))) univ *
          switchVolumeBound D cNorm I widths r U θ Λ +
        6 * ((ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ + p) + (c * Kcap) * ENNReal.ofReal Λ'⁻¹ < 1 := by
    rw [hprodone, mul_one]
    refine lt_of_le_of_lt ?_ hbudget
    gcongr
  exact hcurl ν κ state hstate control hcontrol v r hr Long hLong (ν ⊗ₘ κ) π K
    (ENNReal.ofReal (h / q)) p a h U hh hU T hT point hpoint θ hθ hzero hrectP htime hbroad
    (hae ht) (hae hv) Target (hae hsupport) I centers widths _ hηwidth hcover herror Λ hΛ
    hwidth0 Rb hRb (c * Kcap) hcapP (hae hbox) Λ' hΛ' hbudgetP

end Submission.Obl.k4_physical_row_packet_potential.Switch
