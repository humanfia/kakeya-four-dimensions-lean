import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.NativePrediction
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.KeyFrameBounds
import Submission.Obl.k4_conditional_common_affine_field.GridField
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set Filter
open Inherited.Native

noncomputable section

namespace KeyFrame

/-- An original occupied short key and the prepared block geometry give the beta bound.
The original frame and the original label are used throughout. -/
theorem native_beta_bound {α : Type} [MeasurableSpace α]
    (F : CellFrame) (b : α → Fin 6 → ℝ) (l : α) (key : Fin 3 → ℤ)
    {K χ : ℝ} (hK : 1 ≤ K) (hq : 0 < F.q) (hg : 0 < F.g)
    (hg₁ : F.g ≤ 1) (hqg : F.q ≤ K * F.g) (hχ : 0 < χ) (hχm : χ ≤ F.q * F.g)
    (hkey : slotKey b χ (F.q * F.g) F.t₀ l = key)
    (ht₀ : |F.t₀| ≤ 1) (hc₄ : |F.c 4| ≤ K) (hb₃ : |b l 3| ≤ K)
    (hcenter : |F.c 3 + F.c 0 + (F.t₀ + F.q / 2) * F.c 1| +
      |F.c 4 - (F.t₀ + F.q / 2)| ≤ K * F.q)
    (hQ₀ : |b l 1 + F.t₀ * b l 4 -
      baseY F F.t₀ (b l 0 + F.t₀ * b l 3)| ≤ K * (F.q * F.g))
    (hQmid : |b l 0 + (F.t₀ + F.q / 2) * b l 3 - F.c 0 -
      (F.t₀ + F.q / 2) * F.c 1| ≤ K * F.q) :
    |chartBeta F ((key 1 : ℝ) * χ) ((key 0 : ℝ) * χ)
        ((key 2 : ℝ) * (F.q * F.g)) 0| +
      |chartBeta F ((key 1 : ℝ) * χ) ((key 0 : ℝ) * χ)
        ((key 2 : ℝ) * (F.q * F.g)) 1| ≤ 8 * K ^ 4 := by
  have hv : ⌊b l 3 / χ⌋ = key 0 := by
    have h := congrFun hkey 0
    simpa only [slotKey, Matrix.cons_val_zero] using h
  have hy : ⌊(b l 1 + F.t₀ * b l 4) / (F.q * F.g)⌋ = key 2 := by
    have h := congrFun hkey 2
    simpa [slotKey] using h
  have hZ := label_b0_near hχ hkey
  have hV := Submission.Obl.k4_conditional_common_affine_field.abs_sub_floor_mul_le hχ hv
  have hY := Submission.Obl.k4_conditional_common_affine_field.abs_sub_floor_mul_le
    (mul_pos hq hg) hy
  apply chartBeta_total_bound F hK
  · exact chartBeta_zero_bound F (b l) hK hq hg hχ.le hχm ht₀ hc₄ hZ hV hY hQ₀
  · apply chartBeta_one_bound F (b l) hK hq hg hg₁ hqg hχ.le hχm hc₄ hb₃ hZ hV
    · exact (le_add_of_nonneg_right (abs_nonneg _)).trans hcenter
    · exact (le_add_of_nonneg_left (abs_nonneg _)).trans hcenter
    · exact hQmid

/-- A uniform polynomial bound for every coefficient needed by `ComparedBlock`. -/
theorem native_coefficients_bound (F : CellFrame) (Q : MvPolynomial (Fin 4) ℝ)
    (G : MvPolynomial (Fin 2) ℝ) (χ : ℝ) (key : Fin 3 → ℤ)
    {K H : ℝ} (hK : 1 ≤ K) (hH : 0 ≤ H)
    (hβ : |chartBeta F ((key 1 : ℝ) * χ) ((key 0 : ℝ) * χ)
        ((key 2 : ℝ) * (F.q * F.g)) 0| +
      |chartBeta F ((key 1 : ℝ) * χ) ((key 0 : ℝ) * χ)
        ((key 2 : ℝ) * (F.q * F.g)) 1| ≤ 8 * K ^ 4)
    (hr : ∀ e, |nativeDiscrepancy F Q G χ key e| ≤ H) :
    (∀ e, |baseCoefficients (nativeChartPolynomial F Q G χ key) e| ≤ 3888 * H * K ^ 8) ∧
    (∀ e, |transverseCoefficients (nativeChartPolynomial F Q G χ key) e| ≤
      3888 * H * K ^ 8) := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hK₂ : 1 ≤ K ^ 2 := by nlinarith
  have hK₄ : 1 ≤ K ^ 4 := by nlinarith [sq_nonneg (K ^ 2 - 1)]
  have hbound : 48 * H * (8 * K ^ 4 + 1) ^ 2 ≤ 3888 * H * K ^ 8 := by
    have hsq : (8 * K ^ 4 + 1) ^ 2 ≤ (9 * K ^ 4) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    calc
      _ ≤ 48 * H * (9 * K ^ 4) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  obtain ⟨hp, ht⟩ := chart_prediction_coefficients_bound F hH (by positivity) hβ
    (nativeDiscrepancy F Q G χ key) hr
  exact ⟨fun e => (hp e).trans hbound, fun e => (ht e).trans hbound⟩

/-- Every fixed strict exponent margin pays the original polynomial coefficient cost. -/
theorem eventually_native_coefficient_budget {η ξ ε : ℝ} (hmargin : ξ + 8 * η < ε) :
    ∀ᶠ N : ℝ in atTop, ∀ K H : ℝ, 1 ≤ K → 0 ≤ H → K ≤ N ^ η → H ≤ N ^ ξ →
      3888 * H * K ^ 8 ≤ N ^ ε := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
      3888 hmargin] with N hN hbound
  intro K H hK hH hKpow hHpow
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  calc
    _ ≤ 3888 * N ^ ξ * (N ^ η) ^ 8 := by gcongr
    _ = 3888 * N ^ (ξ + 8 * η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN₀.le, mul_assoc,
        ← Real.rpow_add hN₀]
      congr 2
      ring
    _ ≤ _ := hbound

end KeyFrame

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
