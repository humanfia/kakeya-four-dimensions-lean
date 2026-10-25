/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/RefinementLaws.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.Conditioning

/-!
Exact composition of full assigned trajectory priors and selected incidence
laws. The assignment used to normalize a prior is kept separate from every
later incidence restriction.
-/

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RefinementLaws

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_dyadic_crop_affine_laws.Framework

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The full mass of a child assignment is measured in the original prior. -/
theorem conditionedPrior_apply (ν : Measure X) (A : Set X) (e : X ≃ᵐ Y)
    {B : Set Y} (hB : MeasurableSet B) :
    conditionedPrior ν A e B = (ν A)⁻¹ * ν (A ∩ e ⁻¹' B) := by
  rw [conditionedPrior, Measure.smul_apply, e.measurableEmbedding.map_apply,
    Measure.restrict_apply (hB.preimage e.measurable), inter_comm]
  rfl

/-- The two full-prior denominators multiply to the original nested mass. -/
theorem assignment_mass_mul (ν : Measure X) (A : Set X) (e : X ≃ᵐ Y)
    {B : Set Y} (hB : MeasurableSet B) (hA₀ : ν A ≠ 0) (hAtop : ν A ≠ ∞) :
    ν A * conditionedPrior ν A e B = ν (A ∩ e ⁻¹' B) := by
  rw [conditionedPrior_apply ν A e hB, ← mul_assoc,
    ENNReal.mul_inv_cancel hA₀ hAtop, one_mul]

/-- Conditioning twice on full assignments is conditioning once on their
original intersection. No selected-incidence mass appears in this identity. -/
theorem conditionedPrior_comp (ν : Measure X) (A : Set X)
    (e : X ≃ᵐ Y) (f : Y ≃ᵐ Z) {B : Set Y} (hB : MeasurableSet B)
    (hA₀ : ν A ≠ 0) (hAtop : ν A ≠ ∞) :
    conditionedPrior (conditionedPrior ν A e) B f =
      conditionedPrior ν (A ∩ e ⁻¹' B) (e.trans f) := by
  have hinv₀ : (ν A)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hAtop
  have hinvtop : (ν A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hA₀
  have hscalar : ((ν A)⁻¹ * ν (A ∩ e ⁻¹' B))⁻¹ * (ν A)⁻¹ =
      (ν (A ∩ e ⁻¹' B))⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hinv₀) (Or.inl hinvtop), inv_inv]
    calc
      ν A * (ν (A ∩ e ⁻¹' B))⁻¹ * (ν A)⁻¹ =
          (ν (A ∩ e ⁻¹' B))⁻¹ * (ν A * (ν A)⁻¹) := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hA₀ hAtop, mul_one]
  rw [conditionedPrior, conditionedPrior_apply ν A e hB, conditionedPrior,
    Measure.restrict_smul, Measure.restrict_map e.measurable hB,
    Measure.restrict_restrict (hB.preimage e.measurable),
    Measure.map_smul _ f.measurable.aemeasurable,
    Measure.map_map f.measurable e.measurable, smul_smul,
    inter_comm (e ⁻¹' B), hscalar]
  rfl

/-- Positive finite parent normalization permits exact cancellation even when
the final selected law has zero mass. -/
theorem inverse_budget_comp (a b q₁ q₂ : ℝ≥0∞)
    (ha₀ : a ≠ 0) (hatop : a ≠ ∞) (hq₁₀ : q₁ ≠ 0) (hq₁top : q₁ ≠ ∞) :
    (q₂ * (a⁻¹ * b))⁻¹ * (q₁ * a)⁻¹ = (q₁ * q₂ * b)⁻¹ := by
  rw [mul_comm (q₂ * (a⁻¹ * b))⁻¹,
    ← ENNReal.mul_inv (Or.inl (mul_ne_zero hq₁₀ ha₀))
      (Or.inl (ENNReal.mul_ne_top hq₁top hatop))]
  congr 1
  calc
    q₁ * a * (q₂ * (a⁻¹ * b)) = q₁ * q₂ * (a * a⁻¹) * b := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel ha₀ hatop, mul_one]

/-- Composing two restricted pushforwards retains exactly the original
incidences lying in both selected sets. The displayed normalization still
uses the full assignments `A` and `B`. -/
theorem normalized_incidence_comp
    {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace Ω''] (μ : Measure Ω) (C : Set Ω)
    (Φ : Ω ≃ᵐ Ω') (Ψ : Ω' ≃ᵐ Ω'')
    {C' : Set Ω'} (hC' : MeasurableSet C')
    (ν : Measure X) (A : Set X) (e : X ≃ᵐ Y)
    {B : Set Y} (hB : MeasurableSet B)
    (q₁ q₂ : ℝ≥0∞) (hA₀ : ν A ≠ 0) (hAtop : ν A ≠ ∞)
    (hq₁₀ : q₁ ≠ 0) (hq₁top : q₁ ≠ ∞) :
    (q₂ * conditionedPrior ν A e B)⁻¹ •
        (((q₁ * ν A)⁻¹ • (μ.restrict C).map Φ).restrict C').map Ψ =
      (q₁ * q₂ * ν (A ∩ e ⁻¹' B))⁻¹ •
        (μ.restrict (C ∩ Φ ⁻¹' C')).map (Φ.trans Ψ) := by
  rw [Measure.restrict_smul, Measure.restrict_map Φ.measurable hC',
    Measure.restrict_restrict (hC'.preimage Φ.measurable),
    Measure.map_smul _ Ψ.measurable.aemeasurable,
    Measure.map_map Ψ.measurable Φ.measurable, smul_smul,
    conditionedPrior_apply ν A e hB,
    inverse_budget_comp (ν A) _ q₁ q₂ hA₀ hAtop hq₁₀ hq₁top,
    inter_comm (Φ ⁻¹' C')]
  rfl

/-- The mass identity in the real units used by the mixture weights. -/
theorem assignment_mass_toReal (ν : Measure X) (A : Set X) (e : X ≃ᵐ Y)
    {B : Set Y} (hB : MeasurableSet B) (hA₀ : ν A ≠ 0) (hAtop : ν A ≠ ∞) :
    (ν A).toReal * (conditionedPrior ν A e B).toReal =
      (ν (A ∩ e ⁻¹' B)).toReal := by
  simpa only [ENNReal.toReal_mul] using
    congrArg ENNReal.toReal (assignment_mass_mul ν A e hB hA₀ hAtop)

/-- Normalized child weights collapse to the original weight times the
composite block length and original full assigned mass. -/
theorem mixture_weight_comp (w q₁ q₂ a b m Z₁ Z₂ : ℝ) (hm : a * b = m) :
    ((w * q₁ * a / Z₁) * q₂ * b) / Z₂ =
      w * (q₁ * q₂) * m / (Z₁ * Z₂) := by
  rw [← hm]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The normalizer of a second finite atlas, multiplied by the first
normalizer, is the total original budget of its final assignments. -/
theorem mixture_normalizer_comp {ι κ : Type*} [Fintype κ]
    (parent : κ → ι) (w q₁ a : ι → ℝ) (q₂ b m : κ → ℝ)
    (Z₁ : ℝ) (hZ₁ : Z₁ ≠ 0) (hm : ∀ j, a (parent j) * b j = m j) :
    Z₁ * (∑ j, (w (parent j) * q₁ (parent j) * a (parent j) / Z₁) * q₂ j * b j) =
      ∑ j, w (parent j) * (q₁ (parent j) * q₂ j) * m j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hm j]
  field_simp

/-- A two-layer normalized mixture has exactly the weights obtained by
normalizing its original full-prior budgets once. -/
theorem mixture_weight_original {ι κ : Type*} [Fintype κ]
    (parent : κ → ι) (w q₁ a : ι → ℝ) (q₂ b m : κ → ℝ)
    (Z₁ : ℝ) (hZ₁ : Z₁ ≠ 0) (hm : ∀ j, a (parent j) * b j = m j) (j : κ) :
    ((w (parent j) * q₁ (parent j) * a (parent j) / Z₁) * q₂ j * b j) /
        (∑ j', (w (parent j') * q₁ (parent j') * a (parent j') / Z₁) * q₂ j' * b j') =
      (w (parent j) * (q₁ (parent j) * q₂ j) * m j) /
        (∑ j', w (parent j') * (q₁ (parent j') * q₂ j') * m j') := by
  rw [mixture_weight_comp _ _ _ _ _ _ _ _ (hm j),
    mixture_normalizer_comp parent w q₁ a q₂ b m Z₁ hZ₁ hm]

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RefinementLaws
