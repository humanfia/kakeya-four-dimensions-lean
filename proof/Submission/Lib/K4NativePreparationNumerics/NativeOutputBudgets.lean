/-
Adapted from: here:o204
Native/NativeOutputBudgets.lean, session x0749,
commit c8f98567. Original-reference output pruning and strip-fraction budgets.
-/
import Submission.Lib.K4NativePreparationNumerics.NativeValueCapNumerics

/-! The final original-reference floors pay bounded physical menus and
ordinary-time pruning. The intrinsic strip fraction remains small after
division by that same output floor. -/

namespace Submission.Lib.K4NativePreparationNumerics

noncomputable def nativeOutputStateFloor (N K α : ℝ) : ℝ :=
  N ^ (-α) / K ^ 20

noncomputable def nativeOutputReferenceCount (N K α : ℝ) : ℝ :=
  N ^ α * K ^ 12

theorem native_output_reference_loss {N K α : ℝ} (hN : 0 < N) (hK : 0 < K) :
    nativeOutputStateFloor N K α * nativeOutputReferenceCount N K α = (K ^ 8)⁻¹ := by
  have hcancel : N ^ (-α) * N ^ α = 1 := by
    rw [← Real.rpow_add hN, neg_add_cancel, Real.rpow_zero]
  unfold nativeOutputStateFloor nativeOutputReferenceCount
  calc
    _ = (N ^ (-α) * N ^ α) * (K ^ 12 / K ^ 20) := by ring
    _ = (K ^ 8)⁻¹ := by rw [hcancel]; field_simp

/-- This is an original-prior loss budget; it contains no inverse number
of original packets or native geometry cells. -/
theorem native_output_pruning_budget {N K α κ : ℝ}
    (hN : 0 < N) (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3 * κ ≤ K) :
    nativeOutputStateFloor N K α * nativeOutputReferenceCount N K α +
        (K ^ 20)⁻¹ ≤ κ⁻¹ / 1024 := by
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  have hKpos : 0 < K := by linarith
  have hKone : 1 ≤ K := by linarith
  have h8pos : 0 < K ^ 8 := pow_pos hKpos _
  have h8lower : 2048 * κ ≤ K ^ 8 := by
    have h2 : 2304 * K ≤ K ^ 2 := by nlinarith
    have h28 : K ^ 2 ≤ K ^ 8 := pow_le_pow_right₀ hKone (by norm_num)
    nlinarith
  have h8inv : (K ^ 8)⁻¹ ≤ (2048 * κ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) h8lower
  have h20inv : (K ^ 20)⁻¹ ≤ (K ^ 8)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le h8pos
      (pow_le_pow_right₀ hKone (by norm_num : 8 ≤ 20))
  rw [native_output_reference_loss hN hKpos]
  calc
    _ ≤ 2 * (2048 * κ)⁻¹ := by linarith
    _ = κ⁻¹ / 1024 := by field_simp; norm_num

/-- The concrete 108 physical codes, 5832 quarter cores, two signs and
K^10 value bins fit in K^12 at the pregeometry envelope. -/
theorem native_output_physical_menu_budget {K : ℝ} (hK : 2304 ≤ K) :
    108 * 5832 * 2 * K ^ 10 ≤ K ^ 12 := by
  have hK0 : 0 ≤ K := by linarith
  have hconstant : (108 : ℝ) * 5832 * 2 ≤ K ^ 2 := by nlinarith
  calc
    _ ≤ K ^ 2 * K ^ 10 := mul_le_mul_of_nonneg_right hconstant (pow_nonneg hK0 _)
    _ = K ^ 12 := by ring

theorem native_output_fraction_small {N K α Λ : ℝ}
    (hN : 0 < N) (hK : 0 < K) (hΛ : 0 < Λ)
    (hbudget : K ^ 20 * N ^ α ≤ Λ) :
    (16 * (100000 * Λ)⁻¹) / nativeOutputStateFloor N K α ≤ 1 / 5000 := by
  have hratio : (K ^ 20 * N ^ α) / Λ ≤ 1 := (div_le_one hΛ).2 hbudget
  have hid : (16 * (100000 * Λ)⁻¹) / nativeOutputStateFloor N K α =
      (16 / 100000) * ((K ^ 20 * N ^ α) / Λ) := by
    unfold nativeOutputStateFloor
    rw [Real.rpow_neg hN.le]
    field_simp
  rw [hid]
  calc
    _ ≤ (16 / 100000) * 1 := mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ ≤ 1 / 5000 := by norm_num

/-- The exponent for the original output floor can be chosen after the
refinement exponent. The fixed power of the path factor only helps. -/
theorem native_output_fraction_power_budget {N K α ε κ : ℝ} (q : ℕ)
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hε : 0 ≤ ε)
    (hK : 0 ≤ K) (hKpower : K ≤ N ^ (ε / 80)) (hα : α ≤ ε / 4) :
    K ^ 20 * N ^ α ≤ κ ^ q * N ^ ε := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have h20 : K ^ 20 ≤ N ^ (ε / 4) := by
    calc
      _ ≤ (N ^ (ε / 80)) ^ 20 := pow_le_pow_left₀ hK hKpower _
      _ = _ := by rw [← Real.rpow_mul_natCast hNpos.le]; congr 1; norm_num; ring
  calc
    _ ≤ N ^ (ε / 4) * N ^ (ε / 4) := mul_le_mul h20
      (Real.rpow_le_rpow_of_exponent_le hN hα)
      (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)
    _ = N ^ (ε / 2) := by rw [← Real.rpow_add hNpos]; congr 1; ring
    _ ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ ≤ κ ^ q * N ^ ε := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_pow₀ hκ : 1 ≤ κ ^ q) (Real.rpow_nonneg hNpos.le _)

/-- The union bound for the seven-direction experiment is small on the
retained output states, after paying their original-reference floor. -/
theorem native_output_fraction_gp_small {N K α Λ : ℝ}
    (hN : 0 < N) (hK : 0 < K) (hΛ : 0 < Λ)
    (hbudget : K ^ 20 * N ^ α ≤ Λ) :
    686 * ((ENNReal.ofReal (nativeOutputStateFloor N K α))⁻¹ *
        ENNReal.ofReal (16 * (100000 * Λ)⁻¹)) ≤ (1 / 4 : ENNReal) := by
  have hfloor : 0 < nativeOutputStateFloor N K α := by
    unfold nativeOutputStateFloor
    positivity
  have hsmall := native_output_fraction_small hN hK hΛ hbudget
  have hreal : 686 * ((16 * (100000 * Λ)⁻¹) / nativeOutputStateFloor N K α) ≤
      (1 / 4 : ℝ) := by linarith
  calc
    _ = ENNReal.ofReal
        (686 * ((16 * (100000 * Λ)⁻¹) / nativeOutputStateFloor N K α)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 686), ENNReal.ofReal_ofNat]
      rw [ENNReal.ofReal_div_of_pos hfloor]
      simp only [div_eq_mul_inv, mul_comm]
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := ENNReal.ofReal_le_ofReal hreal
    _ = 1 / 4 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num

end Submission.Lib.K4NativePreparationNumerics
