import Submission.Obl.k4_conditional_common_affine_field.PairWitnesses
import Submission.Lib.K4ScalarCoreTools.Finalization.PolynomialBinSampling
import Submission.Obl.k4_critical_conditional_row_preparation.NativeJointCap

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4ScalarCoreTools.Finalization
open Submission.Obl.k4_critical_conditional_row_preparation (floor_bin_eq_Ico)

/-- Rounding the external palette to its actual fine-bin left endpoints only
doubles the radius in a pencil bound. -/
theorem rounded_palette_thin (π : Measure ℝ) (δ r K S : ℝ)
    (hδ : 0 < δ) (hδr : δ ≤ r) (hr1 : 2*r ≤ 1)
    (hcap : ∀ x s : ℝ, δ ≤ s → s ≤ 1 →
      π (Icc (x-s) (x+s)) ≤ ENNReal.ofReal (K*s^S)) :
    ∀ x : ℝ, ((π.map (fun v => ⌊v/δ⌋)).map (fun j : ℤ => δ*(j : ℝ)))
      {v | |v-x| < r} ≤ ENNReal.ofReal (K*(2*r)^S) := by
  intro x
  have hf : Measurable (fun v : ℝ => ⌊v/δ⌋) := (measurable_id.div_const δ).floor
  have hc : Measurable (fun j : ℤ => δ*(j : ℝ)) := measurable_of_countable _
  have hm : MeasurableSet {v : ℝ | |v-x| < r} :=
    measurableSet_lt (measurable_id.sub_const x).abs measurable_const
  rw [Measure.map_map hc hf, Measure.map_apply (hc.comp hf) hm]
  apply (measure_mono ?_).trans (hcap x (2*r) (by linarith) hr1)
  intro v hv
  have hdist := floor_scaled_error hδ v
  change |δ*(⌊v/δ⌋ : ℝ)-x| < r at hv
  have h := (abs_sub_le v (δ*(⌊v/δ⌋ : ℝ)) x).trans (add_le_add hdist hv.le)
  exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

/-- The frozen conditional fine-bin inequality yields a separated pair of actual
velocity bins on a dense original restriction, without conditioning the source prior. -/
theorem exists_two_velocity_bins {Ω Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [Countable Q] [MeasurableSingletonClass Q] [Nonempty Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (A : Set Ω) (hA : MeasurableSet A) (hμA : ∀ᵐ ω ∂μ, ω ∈ A)
    (state : Ω → Q) (hstate : Measurable state)
    (v : Ω → ℝ) (hv : Measurable v) (π : Measure ℝ) [IsProbabilityMeasure π]
    (δ r K S : ℝ) (hδ : 0 < δ) (hδr : δ ≤ r) (hr1 : 2*r ≤ 1) (hK : 0 < K)
    (hsmall : K^2*(2*r)^S ≤ 1/2)
    (hpalette : ∀ x s : ℝ, δ ≤ s → s ≤ 1 →
      π (Icc (x-s) (x+s)) ≤ ENNReal.ofReal (K*s^S))
    (hcap : ∀ q j, μ {ω | state ω = q ∧ ⌊v ω/δ⌋ = j} ≤
      ENNReal.ofReal K * μ {ω | state ω = q} *
        π (Ico ((j : ℝ)*δ) (((j : ℝ)+1)*δ))) :
    ∃ j : ℤ × ℤ, r ≤ |δ*(j.1 : ℝ)-δ*(j.2 : ℝ)| ∧
      ∃ W : Set Ω, MeasurableSet W ∧ W ⊆ A ∧
        ENNReal.ofReal (1/(2*K^2))*μ univ ≤ μ W ∧
        ∀ ω ∈ W, ∃ a ∈ A, ∃ b ∈ A,
          state a = state ω ∧ state b = state ω ∧
            ⌊v a/δ⌋ = j.1 ∧ ⌊v b/δ⌋ = j.2 := by
  let code : Ω → ℤ := fun ω => ⌊v ω/δ⌋
  have hcode : Measurable code := (hv.div_const δ).floor
  let πc := π.map (fun w : ℝ => ⌊w/δ⌋)
  have hπm : Measurable (fun w : ℝ => ⌊w/δ⌋) := (measurable_id.div_const δ).floor
  have hπc (j : ℤ) : πc {j} = π (Ico ((j : ℝ)*δ) (((j : ℝ)+1)*δ)) := by
    change π.map (fun w : ℝ => ⌊w/δ⌋) {j} = _
    rw [Measure.map_apply hπm (measurableSet_singleton j)]
    exact congrArg π (floor_bin_eq_Ico δ j hδ)
  have hsm : ENNReal.ofReal K * ENNReal.ofReal (K*(2*r)^S) ≤ 1/2 := by
    calc
      _ = ENNReal.ofReal (K^2*(2*r)^S) := by
        rw [← ENNReal.ofReal_mul hK.le]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (1/2 : ℝ) := ENNReal.ofReal_le_ofReal hsmall
      _ = _ := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
  exact exists_two_original_witness_codes μ hμ A hA hμA state hstate code hcode
    (fun j : ℤ => δ*(j : ℝ)) (measurable_of_countable _) πc K r
    (ENNReal.ofReal (K*(2*r)^S)) hK
    (rounded_palette_thin π δ r K S hδ hδr hr1 hpalette) hsm
    (fun q j => by simpa only [hπc] using hcap q j)

end Submission.Obl.k4_conditional_common_affine_field
