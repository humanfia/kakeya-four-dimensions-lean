/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeCalibration.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o218, session x0760, commit ce93c8df6e603b8044f968da8a9087dc728f3bb6,
   `Submission/Obl/k4_horizontal_endpoint_wide_return/NativeCalibration.lean`. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeFrame
import Submission.Obl.k4_quadratic_mesh_coefficient_calibration.RawGridCalibration
import Submission.Lib.K4ChartLifting.Sizes

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

def nativeCalibrationLoss (C H m β : ℝ) : ℝ :=
  128 * C * (64 / (m / (β * (8 * H) ^ 3))) ^ 3

/-- A common original mass factor cancels from the calibration loss. -/
theorem nativeCalibrationLoss_common_factor (C H m β scale : ℝ) (hscale : scale ≠ 0) :
    nativeCalibrationLoss C H (scale * m) (scale * β) = nativeCalibrationLoss C H m β := by
  unfold nativeCalibrationLoss
  rw [show scale * β * (8 * H) ^ 3 = scale * (β * (8 * H) ^ 3) by ring,
    mul_div_mul_left _ _ hscale]

/-- Mesh calibration bounds a native affine field on its whole box from original
witnesses. In applications the same small-width factor in β and m cancels.
There is no initial bound on the coefficients of the affine field. -/
theorem exists_native_affine_comparison :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (x : Ω → Fin 3 → ℝ)
        (a : Fin 4 → ℝ) (h t₀ p r v w τ H σ m β E B : ℝ),
        0 < h → 1 ≤ H → 0 < σ → σ ≤ H → 0 < m → 0 < β →
        m ≤ β * (8 * H) ^ 3 → 0 ≤ E → 1 ≤ B →
        ENNReal.ofReal m ≤ μ univ →
        (∀ q : Fin 3 → ℤ,
          μ {z | (fun i => ⌊nativeFrame h t₀ p r v w τ (x z) i / σ⌋) = q} ≤
            ENNReal.ofReal (β * σ ^ 3)) →
        (∀ᵐ z ∂μ, (∀ i, |nativeFrame h t₀ p r v w τ (x z) i| ≤ H) ∧
          |a 0 + a 1 * x z 0 + a 2 * x z 1 + a 3 * x z 2| ≤ E) →
        L * nativeCalibrationLoss C H m β * σ ≤ 1 / 2 →
        ∀ z : Fin 3 → ℝ, (∀ i, |nativeFrame h t₀ p r v w τ z i| ≤ B) →
          |a 0 + a 1 * z 0 + a 2 * z 1 + a 3 * z 2| ≤
            8 * B * nativeCalibrationLoss C H m β * E := by
  obtain ⟨C, L, hC, hL, hcal⟩ :=
    Submission.Obl.k4_quadratic_mesh_coefficient_calibration.exists_raw_coefficient_bound_from_original_grid 1
  refine ⟨C, L, hC, hL, ?_⟩
  intro Ω _ μ x a h t₀ p r v w τ H σ m β E B hh hH hσ hσH hm hβ hmβ hE hB
    hmass hcap hgood hsmall z hz
  let Q := nativeAffinePolynomial a h t₀ p r v w τ
  have hQ : Q.totalDegree ≤ 1 := nativeAffinePolynomial_degree _ _ _ _ _ _ _ _
  have hgood' : ∀ᵐ z ∂μ,
      (∀ i, |nativeFrame h t₀ p r v w τ (x z) i| ≤ H) ∧
        |eval (nativeFrame h t₀ p r v w τ (x z)) Q| ≤ E := by
    simpa only [Q, eval_nativeAffinePolynomial_frame a hh.ne'] using hgood
  have hρ : 0 ≤ (64 / (m / (β * (8 * H) ^ 3))) ^ 3 := by positivity
  have hmesh : σ / (8 * H) ≤ σ := by
    apply div_le_self hσ.le
    linarith
  have habs : 2 * L * (((1 + 1) ^ 3 : ℕ) : ℝ) * C *
      (32 * (((1 : ℕ) : ℝ) + 1) / (m / (β * (8 * H) ^ 3))) ^ (3 * 1) *
        (σ / (8 * H)) ≤ 1 / 2 := by
    calc
      _ = 16 * L * C * (64 / (m / (β * (8 * H) ^ 3))) ^ 3 * (σ / (8 * H)) := by
        norm_num only <;> ring
      _ ≤ 16 * L * C * (64 / (m / (β * (8 * H) ^ 3))) ^ 3 * σ := by gcongr
      _ ≤ L * nativeCalibrationLoss C H m β * σ := by
        dsimp only [nativeCalibrationLoss]
        nlinarith [mul_nonneg (mul_nonneg hL.le hC.le) (mul_nonneg hρ hσ.le)]
      _ ≤ 1 / 2 := hsmall
  have hcoeff := hcal Ω μ (fun z => nativeFrame h t₀ p r v w τ (x z)) Q hQ
    H σ m β E hH hσ hσH hm hβ hmβ hE hmass hcap hgood' habs
  have hc : ∀ e, |Q.coeff e| ≤ nativeCalibrationLoss C H m β * E := by
    intro e
    convert hcoeff e using 1 <;> dsimp only [nativeCalibrationLoss] <;> norm_num only <;> ring
  have hnorm : coeffL1 Q ≤ 8 * (nativeCalibrationLoss C H m β * E) := by
    simpa using coeffL1_le_of_coeff_le Q hQ _ hc
  rw [← eval_nativeAffinePolynomial_frame a hh.ne' t₀ p r v w τ z]
  calc
    |eval (nativeFrame h t₀ p r v w τ z) Q| ≤ coeffL1 Q * B :=
      abs_eval_le_of_deg_le_one Q hQ _ B hB hz
    _ ≤ (8 * (nativeCalibrationLoss C H m β * E)) * B :=
      mul_le_mul_of_nonneg_right hnorm (zero_le_one.trans hB)
    _ = _ := by ring

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
