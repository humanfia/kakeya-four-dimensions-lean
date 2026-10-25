/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/AffineRestrictedPrior.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.BoundedHiddenCoefficients
import Submission.Obl.k4_scalar_grid_parameter_preparation.LightCodeRestriction
import Submission.Obl.k4_scalar_coefficient_clustering.Bins

/-! Actual restricted affine priors retain the old coefficient ceilings and strict light-bin bounds. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical ENNReal

def scalarAffineCoefficientCell {X : Type*} (a : X → Fin 5 → ℝ) (ξ : ℝ) (q c : ℤ) : Set X :=
  {l | (⌊a l 0 / ξ⌋ : ℤ) = q ∧ a l 1 ∈ scalarVelocityBin ξ c}

def scalarLightCoefficientSet {X : Type*} [MeasurableSpace X]
    (θ : Measure X) (a : X → Fin 5 → ℝ) (π : Measure ℝ) (ξ d δ : ℝ) : Set X :=
  lightCodeSet θ (fun l => scalarMixedCoefficientTag ξ ξ (a l))
    (fun z => ENNReal.ofReal (ξ ^ (1 + d) * δ) * π (scalarVelocityBin ξ (z 1)))

theorem measurableSet_scalarAffineCoefficientCell {X : Type*} [MeasurableSpace X]
    {a : X → Fin 5 → ℝ} (ha : Measurable a) (ξ : ℝ) (q c : ℤ) :
    MeasurableSet (scalarAffineCoefficientCell a ξ q c) := by
  have h₀ := measurableSet_eq_fun (((measurable_pi_apply 0).comp ha).div_const ξ).floor
    (measurable_const : Measurable fun _ : X => q)
  exact h₀.inter ((measurableSet_scalarVelocityBin ξ c).preimage ((measurable_pi_apply 1).comp ha))

theorem measurableSet_scalarLightCoefficientSet {X : Type*} [MeasurableSpace X]
    (θ : Measure X) (a : X → Fin 5 → ℝ) (ha : Measurable a) (π : Measure ℝ) (ξ d δ : ℝ) :
    MeasurableSet (scalarLightCoefficientSet θ a π ξ d δ) :=
  measurableSet_lightCodeSet θ _ _ (fun z =>
    (measurable_scalarMixedCoefficientTag ξ ξ |>.comp ha) (measurableSet_singleton z))

theorem restricted_affine_hidden_ball_cap {X : Type*} [MeasurableSpace X]
    (θ ν : Measure X) (a : X → Fin 5 → ℝ) (ha : Measurable a) (π : Measure ℝ) [IsFiniteMeasure π]
    (ξ ζ B L : ℝ) (hζ : 0 < ζ) (hL : 0 ≤ L) (q c : ℤ)
    (hbounded : ∀ᵐ l ∂θ, ∀ e, |a l e| ≤ B)
    (hν : ν ≤ θ.restrict (scalarAffineCoefficientCell a ξ q c))
    (hcap : ∀ z : Fin 5 → ℤ, θ {l | scalarMixedCoefficientTag ξ ζ (a l) = z} ≤
      ENNReal.ofReal L * π (scalarVelocityBin ξ (z 1))) (b : EuclideanSpace ℝ (Fin 3)) :
    ν {l | boundedScalarHiddenCoefficients B (a l) ∈ Metric.ball b ζ} ≤
      ENNReal.ofReal (216 * L) * π (scalarVelocityBin ξ c) := by
  have hνθ : ν ≤ θ := hν.trans Measure.restrict_le_self
  have hae : (fun l => boundedScalarHiddenCoefficients B (a l)) =ᵐ[ν]
      fun l => scalarHiddenCoefficients (a l) :=
    ae_mono hνθ (boundedScalarHiddenCoefficients_ae_eq θ a B hbounded)
  have hOld : MeasurableSet {l | scalarHiddenCoefficients (a l) ∈ Metric.ball b ζ} :=
    (continuous_scalarHiddenCoefficients.measurable.comp ha) measurableSet_ball
  calc
    _ = ν {l | scalarHiddenCoefficients (a l) ∈ Metric.ball b ζ} :=
      measure_congr (hae.mono fun _ hl => congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v ∈ Metric.ball b ζ) hl)
    _ ≤ (θ.restrict (scalarAffineCoefficientCell a ξ q c))
        {l | scalarHiddenCoefficients (a l) ∈ Metric.ball b ζ} := hν _
    _ = θ {l | scalarHiddenCoefficients (a l) ∈ Metric.ball b ζ ∧
        (⌊a l 0 / ξ⌋ : ℤ) = q ∧ a l 1 ∈ scalarVelocityBin ξ c} := by
      rw [Measure.restrict_apply hOld]
      congr 1
    _ ≤ _ := affine_hidden_coefficient_ball_cap θ a π ξ ζ L hζ hL q c hcap b

theorem restricted_light_affine_hidden_bin_cap {X : Type*} [MeasurableSpace X]
    (θ ν : Measure X) (a : X → Fin 5 → ℝ) (ha : Measurable a) (π : Measure ℝ)
    (ξ B d δ : ℝ) (hξ : 0 < ξ) (hδ : 0 < δ) (q c : ℤ)
    (hbounded : ∀ᵐ l ∂θ, ∀ e, |a l e| ≤ B)
    (hπ : π (scalarVelocityBin ξ c) ≠ 0)
    (hν : ν ≤ θ.restrict (scalarLightCoefficientSet θ a π ξ d δ ∩ scalarAffineCoefficientCell a ξ q c))
    (b : Fin 3 → ℤ) :
    ν {l | Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode ξ
      (boundedScalarHiddenCoefficients B (a l)) = b} <
        ENNReal.ofReal (ξ ^ (1 + d) * δ) * π (scalarVelocityBin ξ c) := by
  let code := fun l => scalarMixedCoefficientTag ξ ξ (a l)
  let τ := fun z : Fin 5 → ℤ => ENNReal.ofReal (ξ ^ (1 + d) * δ) * π (scalarVelocityBin ξ (z 1))
  let full : Fin 5 → ℤ := ![q,c,b 0,b 1,b 2]
  have hcode (z : Fin 5 → ℤ) : MeasurableSet {l | code l = z} :=
    (measurable_scalarMixedCoefficientTag ξ ξ |>.comp ha) (measurableSet_singleton z)
  have hτ : 0 < τ full := by
    change 0 < ENNReal.ofReal (ξ ^ (1 + d) * δ) * π (scalarVelocityBin ξ c)
    exact pos_iff_ne_zero.mpr (mul_ne_zero
      (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos (Real.rpow_pos_of_pos hξ _) hδ)) hπ)
  have hlcap := restrict_lightCodeSet_bin_lt θ code τ hcode full hτ
  have hνθ : ν ≤ θ := hν.trans Measure.restrict_le_self
  have hae : (fun l => boundedScalarHiddenCoefficients B (a l)) =ᵐ[ν]
      fun l => scalarHiddenCoefficients (a l) :=
    ae_mono hνθ (boundedScalarHiddenCoefficients_ae_eq θ a B hbounded)
  have hm : Measurable (fun l => Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode ξ
      (scalarHiddenCoefficients (a l))) :=
    (Submission.Obl.k4_scalar_coefficient_clustering.measurable_coefficientCode ξ).comp
      (continuous_scalarHiddenCoefficients.measurable.comp ha)
  have hOld := measurableSet_eq_fun hm (measurable_const : Measurable fun _ : X => b)
  calc
    _ = ν {l | Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode ξ (scalarHiddenCoefficients (a l)) = b} :=
      measure_congr (hae.mono fun _ hl => congrArg (fun v : EuclideanSpace ℝ (Fin 3) =>
        Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode ξ v = b) hl)
    _ ≤ (θ.restrict (scalarLightCoefficientSet θ a π ξ d δ ∩ scalarAffineCoefficientCell a ξ q c))
        {l | Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode ξ (scalarHiddenCoefficients (a l)) = b} := hν _
    _ ≤ (θ.restrict (lightCodeSet θ code τ)) {l | code l = full} := by
      rw [Measure.restrict_apply hOld,Measure.restrict_apply (hcode full)]
      apply measure_mono
      intro l hl
      refine ⟨?_,hl.2.1⟩
      have hAff : (⌊a l 0 / ξ⌋ : ℤ) = q ∧ a l 1 ∈ scalarVelocityBin ξ c := hl.2.2
      ext e
      fin_cases e
      · simpa [code,scalarMixedCoefficientTag,full] using hAff.1
      · simpa [code,scalarMixedCoefficientTag,scalarVelocityBin,full] using hAff.2
      · simpa [code,scalarMixedCoefficientTag,scalarHiddenCoefficients,full,
          Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode] using congrFun hl.1 0
      · simpa [code,scalarMixedCoefficientTag,scalarHiddenCoefficients,full,
          Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode] using congrFun hl.1 1
      · simpa [code,scalarMixedCoefficientTag,scalarHiddenCoefficients,full,
          Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode] using congrFun hl.1 2
    _ < _ := hlcap

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
