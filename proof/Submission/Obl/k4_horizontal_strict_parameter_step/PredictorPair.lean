/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/PredictorPair.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.PairComparison
import Submission.Obl.k4_horizontal_strict_parameter_step.BudgetedMatching

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

/-- A finite marked comparison in real predictor coordinates. All estimates refer
to the unnormalized comparison law and the same original colour densities. -/
structure PredictorPair (ι Λ Ω : Type*) [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace Ω] where
  μ : Measure Ω
  finite : IsFiniteMeasure μ
  lab : ι → Λ
  h : ι → Fin 6 → ℝ
  src : Ω → ι
  wit : Ω → ι
  src_measurable : Measurable src
  wit_measurable : Measurable wit
  x : Ω → EuclideanSpace ℝ (Fin 3)
  x_measurable : Measurable x
  w : Ω → ℝ
  w_measurable : Measurable w
  Δ : ℝ
  Δ_pos : 0 < Δ
  ρ : Λ → ℝ
  ρ_nonneg : ∀ l, 0 ≤ ρ l
  good : ∀ᵐ p ∂μ, lab (src p) = lab (wit p) ∧ ‖x p‖ ≤ 1 / 2 ∧
    |predictor (h (src p)) (x p 0) (x p 1) (x p 2) - w p| ≤ Δ ∧
    |predictor (h (wit p)) (x p 0) (x p 1) (x p 2) - w p| ≤ Δ
  density_src : ∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
    μ {p | src p = i ∧ x p ∈ U} ≤ ENNReal.ofReal (ρ (lab i)) * volume U
  density_wit : ∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
    μ {p | wit p = i ∧ x p ∈ U} ≤ ENNReal.ofReal (ρ (lab i)) * volume U

namespace PredictorPair

variable {ι Λ Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [DecidableEq Λ] [MeasurableSpace Ω]
  (C : PredictorPair ι Λ Ω)

def support : Set Ω := {p | C.lab (C.src p) = C.lab (C.wit p) ∧ ‖C.x p‖ ≤ 1 / 2 ∧
  |predictor (C.h (C.src p)) (C.x p 0) (C.x p 1) (C.x p 2) - C.w p| ≤ C.Δ ∧
  |predictor (C.h (C.wit p)) (C.x p 0) (C.x p 1) (C.x p 2) - C.w p| ≤ C.Δ}

theorem measurable_support : MeasurableSet C.support := by
  have hh : Measurable C.h := measurable_of_countable C.h
  have hsrc := C.src_measurable
  have hwit := C.wit_measurable
  have hx := C.x_measurable
  have hs : Measurable (fun p => predictor (C.h (C.src p)) (C.x p 0) (C.x p 1) (C.x p 2)) := by
    unfold predictor
    fun_prop
  have hw : Measurable (fun p => predictor (C.h (C.wit p)) (C.x p 0) (C.x p 1) (C.x p 2)) := by
    unfold predictor
    fun_prop
  exact ((C.src_measurable.prodMk C.wit_measurable)
    ((Set.to_countable {ij : ι × ι | C.lab ij.1 = C.lab ij.2}).measurableSet)).inter
    ((measurableSet_le C.x_measurable.norm measurable_const).inter
      ((measurableSet_le (hs.sub C.w_measurable).abs measurable_const).inter
        (measurableSet_le (hw.sub C.w_measurable).abs measurable_const)))

/-- The measurable conull subtype makes the accepted discrepancy interface
pointwise without deleting any mass or modifying a colour threshold. -/
def setup : DiscSetup ι Λ C.support where
  Pm := C.μ.comap (Subtype.val : C.support → Ω)
  lab := C.lab
  φ := fun i => predictorSheet (C.h i)
  src := fun p => C.src p.val
  wit := fun p => C.wit p.val
  x := fun p => C.x p.val
  w := fun p => C.w p.val
  Δ := C.Δ
  ρ := C.ρ
  finite := by
    letI := C.finite
    constructor
    rw [comap_subtype_coe_apply C.measurable_support]
    simpa using measure_lt_top C.μ C.support
  sheet := fun i => predictorSheet_isMatchSheet (C.h i)
  src_meas := fun i => (C.src_measurable.comp measurable_subtype_coe)
    (measurableSet_singleton i)
  wit_meas := fun i => (C.wit_measurable.comp measurable_subtype_coe)
    (measurableSet_singleton i)
  x_meas := C.x_measurable.comp measurable_subtype_coe
  lab_eq := fun p => p.property.1
  x_mem := fun p => p.property.2.1
  Δ_pos := C.Δ_pos
  near_src := fun p => by
    simpa only [predictorSheet_real, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using p.property.2.2.1
  near_wit := fun p => by
    simpa only [predictorSheet_real, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using p.property.2.2.2
  ρ_nonneg := C.ρ_nonneg
  dens_src := fun i U hU => by
    change C.μ.comap (Subtype.val : C.support → Ω)
      (Subtype.val ⁻¹' {p | C.src p = i ∧ C.x p ∈ U}) ≤ _
    rw [fullSubtype_apply C.μ C.measurable_support C.good]
    exact C.density_src i U hU
  dens_wit := fun i U hU => by
    change C.μ.comap (Subtype.val : C.support → Ω)
      (Subtype.val ⁻¹' {p | C.wit p = i ∧ C.x p ∈ U}) ≤ _
    rw [fullSubtype_apply C.μ C.measurable_support C.good]
    exact C.density_wit i U hU

/-- The original pair law inherits the quantitative comparison from its summed
density budget, including colours whose palette mass is zero. -/
theorem budget_comparison {d₀ ε₀ R₀ : ℝ} (p : MatchingScales d₀ ε₀) (J : JetData)
    (hmb : MatchBound p.middle ε₀ R₀) (hR₀ : 2 ≤ R₀)
    {X B Y d : ℝ} (hX : 4 ≤ X) (hXR : R₀ ≤ X) (hXJ : 3 * J.C₂ ≤ X)
    (hXB : budgetMatchingConstant p J ≤ X)
    (hB : 0 ≤ B) (hBX : B ≤ X) (hY : 0 ≤ Y) (hYX : Y ≤ X ^ (p.size + 3))
    (hd : 0 ≤ d) (hdd : d ≤ d₀) (hbudget : (∑ i, C.ρ (C.lab i)) ≤ X ^ 2)
    (hband : ∀ i k, C.μ {v | C.lab (C.src v) = C.lab i ∧
      |predictor (C.h i) (C.x v 0) (C.x v 1) (C.x v 2) - C.w v| ≤
        2 * ((2 * C.Δ * X ^ p.size) * 2 ^ k)} ≤
        ENNReal.ofReal ((B * C.ρ (C.lab i) * Y ^ d) * ((2 : ℝ) ^ d) ^ k)) :
    C.μ {v | ∃ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 2 ∧
      2 * C.Δ * X ^ p.size ≤ |predictor (C.h (C.src v)) (z 0) (z 1) (z 2) -
        predictor (C.h (C.wit v)) (z 0) (z 1) (z 2)|} ≤
      ENNReal.ofReal (X ^ (-5 : ℝ)) := by
  have hb := budgeted_matching p J C.setup hmb hR₀ hX hXR hXJ hXB hB hBX
    hY hYX hd hdd hbudget (by
      intro i k
      change C.μ.comap (Subtype.val : C.support → Ω)
        {v | C.lab (C.src v.val) = C.lab i ∧
          ‖predictorSheet (C.h i) (emb (C.x v.val)) - (C.w v.val : ℂ)‖ ≤ _} ≤ _
      simp only [predictorSheet_real, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      change C.μ.comap (Subtype.val : C.support → Ω)
        (Subtype.val ⁻¹' {v | C.lab (C.src v) = C.lab i ∧
          |predictor (C.h i) (C.x v 0) (C.x v 1) (C.x v 2) - C.w v| ≤
            2 * ((2 * C.Δ * X ^ p.size) * 2 ^ k)}) ≤ _
      rw [fullSubtype_apply C.μ C.measurable_support C.good]
      exact hband i k)
  change C.μ.comap (Subtype.val : C.support → Ω)
    {v | ∃ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 2 ∧
      2 * C.Δ * X ^ p.size ≤
        ‖predictorSheet (C.h (C.src v.val)) (emb z) -
          predictorSheet (C.h (C.wit v.val)) (emb z)‖} ≤ _ at hb
  simp only [predictorSheet_real, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hb
  change C.μ.comap (Subtype.val : C.support → Ω)
    (Subtype.val ⁻¹' {v | ∃ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 2 ∧
      2 * C.Δ * X ^ p.size ≤ |predictor (C.h (C.src v)) (z 0) (z 1) (z 2) -
        predictor (C.h (C.wit v)) (z 0) (z 1) (z 2)|}) ≤ _ at hb
  rw [fullSubtype_apply C.μ C.measurable_support C.good] at hb
  exact hb

end PredictorPair

end

end Submission.Obl.k4_horizontal_strict_parameter_step
