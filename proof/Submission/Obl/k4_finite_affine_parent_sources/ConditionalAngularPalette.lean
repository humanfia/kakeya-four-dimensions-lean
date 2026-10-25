-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.AngularPalette
import Submission.Obl.k4_finite_affine_parent_sources.ModelMeasures

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4AngularCharge
open scoped ENNReal

noncomputable section

/-- An original reference floor pays for conditioning a retained event.
The denominator is its mass before all later restrictions. -/
theorem conditional_event_cap_of_floor {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (R F E : Set Ω) (hE : MeasurableSet E)
    (hR : μ R ≠ 0) (τ C : ℝ≥0∞) (hτ : τ ≠ 0) (hτtop : τ ≠ ⊤)
    (hfloor : τ * μ F ≤ μ R) (hcap : μ (E ∩ R) ≤ C * μ F) :
    nuE μ R E ≤ τ⁻¹ * C := by
  have hreference : μ F ≤ τ⁻¹ * μ R := by
    calc
      μ F = τ⁻¹ * (τ * μ F) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hτ hτtop, one_mul]
      _ ≤ τ⁻¹ * μ R := mul_le_mul' le_rfl hfloor
  have hratio : (μ R)⁻¹ * μ F ≤ τ⁻¹ := by
    calc
      _ ≤ (μ R)⁻¹ * (τ⁻¹ * μ R) := mul_le_mul' le_rfl hreference
      _ = τ⁻¹ := by
        rw [mul_left_comm, ENNReal.inv_mul_cancel hR (measure_ne_top _ _), mul_one]
  rw [nuE, Measure.smul_apply, Measure.restrict_apply hE, smul_eq_mul]
  calc
    _ ≤ (μ R)⁻¹ * (C * μ F) := mul_le_mul' le_rfl hcap
    _ = ((μ R)⁻¹ * μ F) * C := by ring
    _ ≤ _ := mul_le_mul' hratio le_rfl

/-- The major-velocity law of a masked actual parent has a scalar
angular ceiling in any orientation, with its original reference floor. -/
theorem conditioned_linear_native_palette_cap {Ω : Type} {O : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace O] [MeasurableEq O]
    (μ : Measure Ω) [IsFiniteMeasure μ] (obs : Ω → O) (hobs : Measurable obs)
    (velocity : Ω → EuclideanSpace ℝ (Fin 2)) (fine : ℝ)
    (hcell : Measurable (fun z => fun e : Fin 2 => ⌊velocity z e / fine⌋))
    (lam : Measure O) [SigmaFinite lam] (g : O → ℝ≥0∞) (hg : Measurable g)
    (hmap : μ.map obs = lam.withDensity g)
    (G : O × (Fin 2 → ℤ) → ℝ≥0∞) (hG : Measurable G)
    (hmapG : μ.map (fun z => (obs z, fun e : Fin 2 => ⌊velocity z e / fine⌋)) =
      (lam.prod Measure.count).withDensity G)
    (F R : Set Ω) (hF : MeasurableSet F) (hR : μ R ≠ 0)
    (θ α β τ : ℝ≥0∞) (hθ : θ ≠ 0) (hβ : β ≠ 0) (hτ : τ ≠ 0) (hτtop : τ ≠ ⊤)
    (hfloor : τ * μ F ≤ μ R)
    (hmask : R ⊆ F ∩ {z | θ ≤ labelShare μ obs F z} ∩
      {z | G (obs z, fun e : Fin 2 => ⌊velocity z e / fine⌋) ≤ α ∧ β ≤ g (obs z)})
    (b : Ω → Fin 2 → ℝ) (hb : Measurable (fun z => b z 0))
    (offset : Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (H a : ℝ) (hH : 0 ≤ H) (ha : 0 < a) (hf : 0 < fine) (haf : a ≤ fine)
    (hmajor : ∀ e, |M e 0| ≤ H) (hminor : ∀ e, |M e 1| ≤ a)
    (hcoord : ∀ z ∈ F, ∀ e, velocity z e = offset e + ∑ i, M e i * b z i)
    (hbound : ∀ z ∈ F, |b z 1| ≤ H) (j : ℤ) :
    nuE μ R {z | ⌊b z 0 / a⌋ = j} ≤
      τ⁻¹ * (ENNReal.ofReal ((6 * H + 2) ^ 2) * ((α / β) / θ)) := by
  apply conditional_event_cap_of_floor μ R F _
    ((hb.div_const a).floor (measurableSet_singleton j)) hR τ _ hτ hτtop hfloor
  have hnum := linear_native_palette_cap μ obs hobs velocity fine hcell lam g hg hmap
    G hG hmapG F hF θ α β hθ hβ b offset M H a hH ha hf haf hmajor hminor hcoord hbound j
  have hsub : {z | ⌊b z 0 / a⌋ = j} ∩ R ⊆
      F ∩ {z | θ ≤ labelShare μ obs F z} ∩
        {z | G (obs z, fun e : Fin 2 => ⌊velocity z e / fine⌋) ≤ α ∧ β ≤ g (obs z)} ∩
        {z | ⌊b z 0 / a⌋ = j} := by
    intro z hz
    exact ⟨hmask hz.2, hz.1⟩
  exact (measure_mono hsub).trans (by simpa only [mul_assoc] using hnum)

end
end Submission.Obl.k4_finite_affine_parent_sources
