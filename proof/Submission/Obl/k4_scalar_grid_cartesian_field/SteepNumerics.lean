import Mathlib

namespace Submission.Obl.k4_scalar_grid_cartesian_field

/-- The fine base-cell count and four original code neighborhoods cost a fixed polynomial. -/
theorem steep_code_count_bound {N K : ℝ} (hN : 0 < N) (hK : 1 ≤ K) (B : ENNReal) :
    ENNReal.ofReal (49 * K ^ 2 * (N ^ (-10 : ℝ))⁻¹ ^ 2) *
      (((2 * ⌈2 * K + 1⌉₊ + 1) ^ 4 : ℕ) * B) ≤
        ENNReal.ofReal (400000 * K ^ 6 * N ^ (20 : ℝ)) * B := by
  let M : ℕ := (2 * ⌈2 * K + 1⌉₊ + 1) ^ 4
  have hnum : (M : ℝ) ≤ 6561 * K ^ 4 := by
    have hc := (Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * K + 1)).le
    dsimp [M]
    push_cast
    calc
      _ ≤ (9 * K) ^ 4 := by gcongr; linarith
      _ = _ := by ring
  have hξ : (N ^ (-10 : ℝ))⁻¹ ^ 2 = N ^ (20 : ℝ) := by
    rw [← Real.rpow_neg hN.le, ← Real.rpow_mul_natCast hN.le]
    norm_num
  have hreal : (49 * K ^ 2 * (N ^ (-10 : ℝ))⁻¹ ^ 2) * (M : ℝ) ≤
      400000 * K ^ 6 * N ^ (20 : ℝ) := by
    rw [hξ]
    calc
      _ ≤ (49 * K ^ 2 * N ^ (20 : ℝ)) * (6561 * K ^ 4) := by gcongr
      _ = 321489 * K ^ 6 * N ^ (20 : ℝ) := by ring
      _ ≤ _ := by gcongr; norm_num
  calc
    _ = ENNReal.ofReal ((49 * K ^ 2 * (N ^ (-10 : ℝ))⁻¹ ^ 2) * (M : ℝ)) * B := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 49 * K ^ 2 * (N ^ (-10 : ℝ))⁻¹ ^ 2),
        ENNReal.ofReal_natCast, mul_assoc]
      dsimp only [M]
      ac_rfl
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

/-- Multiply the original spatial numerator by the original angular prior cap. -/
theorem steep_rectangular_cap_product {N K r d S b : ℝ} (hN : 0 < N) (hK : 0 ≤ K) :
    ENNReal.ofReal (K * N ^ (-2 * r - d)) * ENNReal.ofReal (K * N ^ (-S * b)) =
      ENNReal.ofReal (K ^ 2 * N ^ (-2 * r - d - S * b)) := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ K * N ^ (-2 * r - d))]
  congr 1
  calc
    _ = K ^ 2 * (N ^ (-2 * r - d) * N ^ (-S * b)) := by ring
    _ = _ := by rw [← Real.rpow_add hN]; congr 2; ring

/-- The fine base exponent cancels, leaving the two horizon dimensions and the angular gain. -/
theorem steep_mass_normalization {N K κ d S b : ℝ} (hN : 0 < N) (hK : 0 ≤ K) :
    ENNReal.ofReal (400000 * K ^ 6 * N ^ (20 : ℝ)) *
      ENNReal.ofReal (K ^ 2 * N ^ (-2 * (10 + κ) - d - S * b)) =
      ENNReal.ofReal (400000 * K ^ 8 * N ^ (-2 * κ - d - S * b)) := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 400000 * K ^ 6 * N ^ (20 : ℝ))]
  congr 1
  calc
    _ = 400000 * K ^ 8 * (N ^ (20 : ℝ) * N ^ (-2 * (10 + κ) - d - S * b)) := by ring
    _ = _ := by rw [← Real.rpow_add hN]; congr 2; ring

/-- Calibrate steep deletion to the full original `h * ν(A)` packet budget. -/
theorem steep_mass_prior_calibration {N K κ d S b h : ℝ}
    (hN : 0 < N) (hK : 1 ≤ K) (hh : 0 < h) (hscale : N ^ (-κ) / K ≤ h)
    (m : ENNReal) (hfloor : ENNReal.ofReal (N ^ (-d) * h / K) ≤ m) :
    ENNReal.ofReal (400000 * K ^ 8 * N ^ (-2 * κ - d - S * b)) ≤
      ENNReal.ofReal (400000 * K ^ 11 * N ^ (-S * b)) * (ENNReal.ofReal h * m) := by
  have hKpos : 0 < K := by linarith
  have hq : N ^ (-κ) ≤ K * h := by
    have hsc := (div_le_iff₀ hKpos).mp hscale
    nlinarith
  have hpowers : N ^ (-2 * κ - d - S * b) = (N ^ (-κ)) ^ 2 * N ^ (-d) * N ^ (-S * b) := by
    rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  have hreal : 400000 * K ^ 8 * N ^ (-2 * κ - d - S * b) ≤
      (400000 * K ^ 11 * N ^ (-S * b)) * h * (N ^ (-d) * h / K) := by
    rw [hpowers]
    calc
      _ ≤ 400000 * K ^ 8 * ((K * h) ^ 2 * N ^ (-d) * N ^ (-S * b)) := by gcongr
      _ = _ := by field_simp
  calc
    _ ≤ ENNReal.ofReal ((400000 * K ^ 11 * N ^ (-S * b)) * h * (N ^ (-d) * h / K)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (400000 * K ^ 11 * N ^ (-S * b)) *
        (ENNReal.ofReal h * ENNReal.ofReal (N ^ (-d) * h / K)) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (400000 * K ^ 11 * N ^ (-S * b)) * h),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 400000 * K ^ 11 * N ^ (-S * b)), mul_assoc]
    _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl hfloor)

/-- A fixed angular power gain beats every original graph-mass subpower loss. -/
theorem steep_loss_le_inverse_floor {N K H S b : ℝ} (hN : 0 < N) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hnum : 3200000 * (K * H) ^ 12 ≤ N ^ (S * b)) :
    400000 * K ^ 11 * N ^ (-S * b) ≤ 1 / (8 * H) := by
  have hHp : 0 < H := by linarith
  have hpol : K ^ 11 * H ≤ (K * H) ^ 12 := by
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_right₀ hK (show 11 ≤ 12 by norm_num))
      (by simpa only [pow_one] using pow_le_pow_right₀ hH (show 1 ≤ 12 by norm_num))
      (by linarith) (by positivity)
  apply (le_div_iff₀ (by positivity : 0 < 8 * H)).mpr
  calc
    _ = (3200000 * (K ^ 11 * H)) * N ^ (-S * b) := by ring
    _ ≤ (3200000 * (K * H) ^ 12) * N ^ (-S * b) := by gcongr
    _ ≤ N ^ (S * b) * N ^ (-S * b) := mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg hN.le _)
    _ = 1 := by rw [← Real.rpow_add hN]; simp

noncomputable def nonsteepBudget (K Q : ℝ) : ℝ := 10000 * (K * Q) ^ 3

/-- One explicit polynomial controls base confinement, layer errors and both partial derivatives. -/
theorem nonsteepBudget_bounds {K Q : ℝ} (hK : 1 ≤ K) (hQ : 1 ≤ Q) :
    1 ≤ nonsteepBudget K Q ∧ 2 * K ≤ nonsteepBudget K Q ∧
      3000 * K ^ 3 ≤ nonsteepBudget K Q ∧ Q ≤ nonsteepBudget K Q ∧
      30 * K ^ 2 + K * Q ≤ nonsteepBudget K Q := by
  have hKpos : 0 ≤ K := by linarith
  have hQpos : 0 ≤ Q := by linarith
  have hKX : K ≤ K * Q := le_mul_of_one_le_right hKpos hQ
  have hQX : Q ≤ K * Q := le_mul_of_one_le_left hQpos hK
  have hX : 1 ≤ K * Q := one_le_mul_of_one_le_of_one_le hK hQ
  have hXpow : 1 ≤ (K * Q) ^ 3 := one_le_pow₀ hX
  have hXcube : K * Q ≤ (K * Q) ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hX (show 1 ≤ 3 by norm_num)
  have hKsq : K ^ 2 ≤ (K * Q) ^ 3 :=
    (pow_le_pow_left₀ hKpos hKX 2).trans (pow_le_pow_right₀ hX (show 2 ≤ 3 by norm_num))
  have hKcube : K ^ 3 ≤ (K * Q) ^ 3 := pow_le_pow_left₀ hKpos hKX 3
  unfold nonsteepBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Recover the first partial from a directional derivative and the bounded transverse partial. -/
theorem first_partial_of_directional {A B V K Q : ℝ} (hK : 0 ≤ K)
    (hdir : |A + V * B| ≤ 30 * K ^ 2) (hV : |V| ≤ K) (hB : |B| ≤ Q) :
    |A| ≤ 30 * K ^ 2 + K * Q := by
  calc
    _ = |(A + V * B) - V * B| := by congr 1; ring
    _ ≤ |A + V * B| + |V * B| := abs_sub _ _
    _ ≤ 30 * K ^ 2 + K * Q := by
      rw [abs_mul]
      exact add_le_add hdir (mul_le_mul hV hB (abs_nonneg _) hK)

end Submission.Obl.k4_scalar_grid_cartesian_field
