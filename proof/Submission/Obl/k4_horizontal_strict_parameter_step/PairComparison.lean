/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/PairComparison.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.PredictorMatching
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.DyadicMatching

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

/-- Passing to a measurable conull support preserves every original event. -/
theorem fullSubtype_apply {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {G : Set Ω} (hG : MeasurableSet G) (hfull : ∀ᵐ p ∂μ, p ∈ G) (B : Set Ω) :
    μ.comap (Subtype.val : G → Ω) (Subtype.val ⁻¹' B) = μ B := by
  rw [(MeasurableEmbedding.subtype_coe hG).comap_preimage, Subtype.range_coe]
  apply measure_congr
  filter_upwards [hfull] with p hp
  simp [hp]


/-- The accepted discrepancy theorem applies directly to original finite pair laws.
The support tests are only almost everywhere: the conull subtype introduces no mass loss
and no normalization of either original marginal. -/
theorem predictor_pair_comparison
    {ι Λ Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [DecidableEq Λ] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (lab : ι → Λ) (h : ι → Fin 6 → ℝ)
    (src wit : Ω → ι) (hs : Measurable src) (hw : Measurable wit)
    (x : Ω → EuclideanSpace ℝ (Fin 3)) (hx : Measurable x)
    (w : Ω → ℝ) (hmw : Measurable w) (Δ : ℝ) (hΔ : 0 < Δ) (ρ : Λ → ℝ)
    (hρ₀ : ∀ l, 0 ≤ ρ l)
    (hgood : ∀ᵐ p ∂μ, lab (src p) = lab (wit p) ∧ ‖x p‖ ≤ 1 / 2 ∧
      |predictor (h (src p)) (x p 0) (x p 1) (x p 2) - w p| ≤ Δ ∧
      |predictor (h (wit p)) (x p 0) (x p 1) (x p 2) - w p| ≤ Δ)
    (hdens_src : ∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
      μ {p | src p = i ∧ x p ∈ U} ≤ ENNReal.ofReal (ρ (lab i)) * volume U)
    (hdens_wit : ∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
      μ {p | wit p = i ∧ x p ∈ U} ≤ ENNReal.ofReal (ρ (lab i)) * volume U)
    (J : JetData) (M : ℝ) (θ G : Λ → ℝ) {d₀ ε₀ R₀ ε χ d : ℝ}
    (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hM : 0 < M)
    (hχ : 0 < χ) (hχ1 : χ < 1) (hθ : ∀ l, 0 < θ l) (hG : ∀ l, 0 ≤ G l)
    (hR : R₀ * (2 * Δ) ≤ M) (hC : 3 * J.C₂ ≤ (M / (2 * Δ)) ^ ε)
    (hρ : ∀ l, ρ l * (M / (2 * Δ)) ^ (-ε) ≤ θ l / 2)
    (hρgrow : (2 : ℝ) ^ (-ε) ≤ χ)
    (hΓ : ∀ l, G l / θ l ≤ (M / (2 * Δ)) ^ (d₀ + ε))
    (hΓgrow : (2 : ℝ) ^ d ≤ χ * (2 : ℝ) ^ (d₀ + ε))
    (hband : ∀ i k, μ {p | lab (src p) = lab i ∧
      |predictor (h i) (x p 0) (x p 1) (x p 2) - w p| ≤ 2 * (M * 2 ^ k)} ≤
        ENNReal.ofReal (G (lab i) * ((2 : ℝ) ^ d) ^ k)) :
    μ {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
      M ≤ |predictor (h (src p)) (y 0) (y 1) (y 2) -
        predictor (h (wit p)) (y 0) (y 1) (y 2)|} ≤
      ENNReal.ofReal (4 *
        (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
          (1 - χ) * ∑ i, θ (lab i)) := by
  let V : Set Ω := {p | lab (src p) = lab (wit p) ∧ ‖x p‖ ≤ 1 / 2 ∧
    |predictor (h (src p)) (x p 0) (x p 1) (x p 2) - w p| ≤ Δ ∧
    |predictor (h (wit p)) (x p 0) (x p 1) (x p 2) - w p| ≤ Δ}
  have hhm : Measurable h := measurable_of_countable h
  have hsm : Measurable (fun p => predictor (h (src p)) (x p 0) (x p 1) (x p 2)) := by
    unfold predictor
    fun_prop
  have hwm : Measurable (fun p => predictor (h (wit p)) (x p 0) (x p 1) (x p 2)) := by
    unfold predictor
    fun_prop
  have hV : MeasurableSet V := by
    apply MeasurableSet.inter
      ((hs.prodMk hw) ((Set.to_countable {ij : ι × ι | lab ij.1 = lab ij.2}).measurableSet))
    exact (measurableSet_le hx.norm measurable_const).inter
      ((measurableSet_le (hsm.sub hmw).abs measurable_const).inter
        (measurableSet_le (hwm.sub hmw).abs measurable_const))
  let ν := μ.comap (Subtype.val : V → Ω)
  have hν : IsFiniteMeasure ν := by
    constructor
    rw [show ν univ = μ V by
      dsimp only [ν]
      rw [comap_subtype_coe_apply hV]
      simp]
    exact measure_lt_top μ V
  let S : DiscSetup ι Λ V := {
    Pm := ν
    lab := lab
    φ := fun i => predictorSheet (h i)
    src := fun p => src p.val
    wit := fun p => wit p.val
    x := fun p => x p.val
    w := fun p => w p.val
    Δ := Δ
    ρ := ρ
    finite := hν
    sheet := fun i => predictorSheet_isMatchSheet (h i)
    src_meas := fun i => ((hs.comp measurable_subtype_coe) (measurableSet_singleton i))
    wit_meas := fun i => ((hw.comp measurable_subtype_coe) (measurableSet_singleton i))
    x_meas := hx.comp measurable_subtype_coe
    lab_eq := fun p => p.property.1
    x_mem := fun p => p.property.2.1
    Δ_pos := hΔ
    near_src := fun p => by
      simpa only [predictorSheet_real, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using p.property.2.2.1
    near_wit := fun p => by
      simpa only [predictorSheet_real, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using p.property.2.2.2
    ρ_nonneg := hρ₀
    dens_src := fun i U hU => by
      change μ.comap (Subtype.val : V → Ω)
        (Subtype.val ⁻¹' {p | src p = i ∧ x p ∈ U}) ≤ _
      rw [fullSubtype_apply μ hV hgood]
      exact hdens_src i U hU
    dens_wit := fun i U hU => by
      change μ.comap (Subtype.val : V → Ω)
        (Subtype.val ⁻¹' {p | wit p = i ∧ x p ∈ U}) ≤ _
      rw [fullSubtype_apply μ hV hgood]
      exact hdens_wit i U hU }
  have hb := discrepancy_mass_le_from_base J S M θ G hmb hR₀ hε hεε₀ hM
    hχ hχ1 hθ hG hR hC hρ hρgrow hΓ hΓgrow (by
      intro i k
      change ν {p | lab (src p.val) = lab i ∧
        ‖predictorSheet (h i) (emb (x p.val)) - (w p.val : ℂ)‖ ≤ 2 * (M * 2 ^ k)} ≤ _
      simp only [predictorSheet_real, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      change μ.comap (Subtype.val : V → Ω)
        (Subtype.val ⁻¹' {p | lab (src p) = lab i ∧
          |predictor (h i) (x p 0) (x p 1) (x p 2) - w p| ≤ 2 * (M * 2 ^ k)}) ≤ _
      rw [fullSubtype_apply μ hV hgood]
      exact hband i k)
  change ν {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
    M ≤ ‖predictorSheet (h (src p.val)) (emb y) -
      predictorSheet (h (wit p.val)) (emb y)‖} ≤ _ at hb
  simp only [predictorSheet_real, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hb
  change μ.comap (Subtype.val : V → Ω)
    (Subtype.val ⁻¹' {p | ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 ∧
      M ≤ |predictor (h (src p)) (y 0) (y 1) (y 2) -
        predictor (h (wit p)) (y 0) (y 1) (y 2)|}) ≤ _ at hb
  rw [fullSubtype_apply μ hV hgood] at hb
  exact hb

end

end Submission.Obl.k4_horizontal_strict_parameter_step
