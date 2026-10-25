import Mathlib

namespace Submission.Obl.k4_native_base_flattening

open scoped ENNReal

lemma inverse_power_exception_budget {n : ℝ} (hn : 2 ≤ n) :
    2 * (n ^ 10)⁻¹ + (n ^ 4)⁻¹ ≤ n⁻¹ := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have h3 : (8 : ℝ) ≤ n ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn 3
    norm_num at hh
    exact hh
  have h6 : 1 ≤ n ^ 6 := one_le_pow₀ hn1
  have hmain : 2 + n ^ 6 ≤ n ^ 9 := by
    have hh := mul_le_mul_of_nonneg_left h3 (pow_nonneg hn0.le 6)
    nlinarith
  calc
    _ = (2 + n ^ 6) / n ^ 10 := by field_simp
    _ ≤ n ^ 9 / n ^ 10 := div_le_div_of_nonneg_right hmain (by positivity)
    _ = _ := by field_simp

lemma cutoff_power_bound {n : ℝ} (hn : 2 ≤ n) (E C : ℕ) (hC : E + 4 ≤ C) :
    (n ^ C)⁻¹ * n ^ E ≤ (n ^ 4)⁻¹ := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hp : n ^ (E + 4) ≤ n ^ C := pow_le_pow_right₀ hn1 hC
  have hi : (n ^ C)⁻¹ ≤ (n ^ (E + 4))⁻¹ :=
    (inv_le_inv₀ (pow_pos hn0 C) (pow_pos hn0 (E + 4))).2 hp
  calc
    _ ≤ (n ^ (E + 4))⁻¹ * n ^ E := mul_le_mul_of_nonneg_right hi (by positivity)
    _ = _ := by rw [pow_add]; field_simp

/-- Once the cutoff exponent exceeds the support-volume exponent by four, the
L1 error at power ten and the cutoff mass fit the frozen power-one exception budget. -/
theorem observation_exception_budget {n : ℝ} (hn : 2 ≤ n) (E C : ℕ)
    (hC : E + 4 ≤ C) (δ V : ENNReal)
    (hδ : δ ≤ ENNReal.ofReal ((n ^ (10 : ℕ))⁻¹))
    (hV : V ≤ ENNReal.ofReal (n ^ E)) :
    2 * δ + ENNReal.ofReal (n ^ (-(C : ℝ))) * V ≤
      ENNReal.ofReal (n ^ (-1 : ℝ)) := by
  have hn0 : 0 < n := by linarith
  have hcut : n ^ (-(C : ℝ)) = (n ^ C)⁻¹ := by
    rw [Real.rpow_neg hn0.le, Real.rpow_natCast]
  have hlast : n ^ (-1 : ℝ) = n⁻¹ := by
    rw [Real.rpow_neg hn0.le, Real.rpow_one]
  rw [hcut, hlast]
  calc
    _ ≤ 2 * ENNReal.ofReal ((n ^ (10 : ℕ))⁻¹) +
        ENNReal.ofReal ((n ^ C)⁻¹) * ENNReal.ofReal (n ^ E) := by gcongr
    _ = ENNReal.ofReal (2 * (n ^ 10)⁻¹ + (n ^ C)⁻¹ * n ^ E) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (2 * (n ^ 10)⁻¹ + (n ^ 4)⁻¹) :=
      ENNReal.ofReal_le_ofReal (add_le_add_right (cutoff_power_bound hn E C hC) _)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (inverse_power_exception_budget hn)

end Submission.Obl.k4_native_base_flattening
