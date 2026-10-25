import Submission.Obl.k4_compatible_pair_frame_preparation.FramePowers

namespace Submission.Obl.k4_compatible_pair_frame_preparation

private theorem large_one {X : ℝ} (hX : (2 : ℝ) ^ 100 ≤ X) : 1 ≤ X := by
  norm_num at hX ⊢
  linarith

/-- Extrapolation over the coarse time block has a universal power cost. -/
theorem coarse_value_factor_le {X K q : ℝ} (hX : (2 : ℝ) ^ 100 ≤ X)
    (hK0 : 0 ≤ K) (hK : K ≤ X) (hq0 : 0 ≤ q) (hq : q ≤ 2 * X) :
    12 * K * (q + 1) ^ 2 ≤ X ^ 4 := by
  have hX1 := large_one hX
  have hq1 : q + 1 ≤ 3 * X := by linarith
  calc
    12 * K * (q + 1) ^ 2 ≤ 12 * X * (3 * X) ^ 2 := by gcongr
    _ = 108 * X ^ 3 := by ring
    _ ≤ X * X ^ 3 := by gcongr; norm_num at hX; linarith
    _ = X ^ 4 := by ring

/-- Hidden-bin multiplicity is controlled after including the native derivative floor. -/
theorem hidden_bin_factor_le {X K q b : ℝ} (hX : (2 : ℝ) ^ 100 ≤ X)
    (hK0 : 0 ≤ K) (hK : K ≤ X) (hq0 : 0 ≤ q) (hq : q ≤ 2 * X)
    (hb : 0 < b) (hbi : b⁻¹ ≤ X) :
    16 * (1 + 12 * K * (q + 1) ^ 2 / b) ≤ X ^ 6 := by
  have hX1 := large_one hX
  have hv := coarse_value_factor_le hX hK0 hK hq0 hq
  have hX5 : 1 ≤ X ^ 5 := one_le_pow₀ hX1
  calc
    16 * (1 + 12 * K * (q + 1) ^ 2 / b) ≤ 16 * (1 + X ^ 4 * X) := by
      rw [div_eq_mul_inv]
      gcongr
    _ ≤ 32 * X ^ 5 := by nlinarith
    _ ≤ X * X ^ 5 := by gcongr; norm_num at hX; linarith
    _ = X ^ 6 := by ring

/-- The common-frame Jacobian, relative to the native scale product. -/
theorem frame_jacobian_le {X K κ q Afr V r₁ r₂ : ℝ}
    (hX : (2 : ℝ) ^ 100 ≤ X) (hK0 : 0 ≤ K) (hK : K ≤ X)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ X) (hq0 : 0 ≤ q) (hq : q ≤ 2 * X)
    (hAfr0 : 0 ≤ Afr) (hAfr : Afr ≤ 626 * K)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hV : V ≤ Afr ^ 2 * q ^ 2 * (8 * X) * (r₁ * r₂)) :
    (100 * κ) ^ 3 * V ≤ X ^ 9 * (r₁ * r₂) := by
  have hX1 := large_one hX
  have hAfrX : Afr ≤ 626 * X := hAfr.trans (by gcongr)
  calc
    (100 * κ) ^ 3 * V ≤ (100 * κ) ^ 3 * (Afr ^ 2 * q ^ 2 * (8 * X) * (r₁ * r₂)) := by
      gcongr
    _ ≤ (100 * X) ^ 3 * ((626 * X) ^ 2 * (2 * X) ^ 2 * (8 * X) * (r₁ * r₂)) := by
      gcongr
    _ = 12540032000000 * X ^ 8 * (r₁ * r₂) := by ring
    _ ≤ X * X ^ 8 * (r₁ * r₂) := by gcongr; norm_num at hX; linarith
    _ = X ^ 9 * (r₁ * r₂) := by ring

/-- The density budget has a fixed universal loss, independent of format exponents. -/
theorem frame_density_coefficient_le {X K κ q Afr V r₁ r₂ n A b : ℝ}
    (hX : (2 : ℝ) ^ 100 ≤ X) (hK0 : 0 ≤ K) (hK : K ≤ X)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ X) (hq0 : 0 ≤ q) (hq : q ≤ 2 * X)
    (hAfr0 : 0 ≤ Afr) (hAfr : Afr ≤ 626 * K)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hn : 0 ≤ n) (hA0 : 0 ≤ A) (hA : A ≤ X)
    (hb : 0 < b) (hbi : b⁻¹ ≤ X) (hV0 : 0 ≤ V)
    (hV : V ≤ Afr ^ 2 * q ^ 2 * (8 * X) * (r₁ * r₂)) :
    (n * A) * (16 * (1 + 12 * K * (q + 1) ^ 2 / b)) * ((100 * κ) ^ 3 * V) ≤
      (n * r₁ * r₂) * X ^ 100 := by
  have hX1 := large_one hX
  have hh := hidden_bin_factor_le hX hK0 hK hq0 hq hb hbi
  have hj := frame_jacobian_le hX hK0 hK hκ0 hκ hq0 hq hAfr0 hAfr hr₁ hr₂ hV
  calc
    _ ≤ (n * X) * X ^ 6 * (X ^ 9 * (r₁ * r₂)) := by gcongr
    _ = (n * r₁ * r₂) * X ^ 16 := by ring
    _ ≤ (n * r₁ * r₂) * X ^ 100 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (show 16 ≤ 100 by omega)) (by positivity)

/-- Entry count times the common sigma has only a third-power cost. -/
theorem frame_count_coefficient_le {X q κ : ℝ} (hX : 2 ≤ X)
    (hq0 : 0 ≤ q) (hq : q ≤ 2 * X) (hκ0 : 0 ≤ κ) (hκ : κ ≤ X) :
    q * κ ≤ X ^ 3 := by
  calc
    q * κ ≤ 2 * X ^ 2 := by nlinarith
    _ ≤ X ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg X) (sub_nonneg.mpr hX)]

end Submission.Obl.k4_compatible_pair_frame_preparation
