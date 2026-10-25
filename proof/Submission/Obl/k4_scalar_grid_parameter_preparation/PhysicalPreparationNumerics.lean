/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PhysicalPreparationNumerics.lean -/
import Mathlib

/-! Uniform polynomial budgets for the scalar physical-support preparation. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

theorem scalar_fine_mesh_budget (K z q : ℝ) (hK : 1 ≤ K) (hz : 1 ≤ z) (hq : 0 < q)
    (horizon : q ≤ K * z) (hbudget : 49766400 * K ^ 13 ≤ z) :
    (z⁻¹) ^ 10 ≤ q⁻¹ ∧
      162 * (1200 * K * (2 * K / q⁻¹) ^ 4) * (2 * K) ^ 4 * (z⁻¹) ^ 10 ≤ z⁻¹ := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hzpos : 0 < z := zero_lt_one.trans_le hz
  have hK13 : K ≤ K ^ 13 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ 13 by norm_num)
  have hKz : K ≤ z := by nlinarith [pow_nonneg hK₀ 13]
  have hqz : q ≤ z ^ 2 := by
    exact horizon.trans ((mul_le_mul_of_nonneg_right hKz hzpos.le).trans_eq (by ring))
  constructor
  · rw [inv_pow]
    calc
      (z ^ 10)⁻¹ ≤ (z ^ 2)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hzpos 2)
          (pow_le_pow_right₀ hz (show 2 ≤ 10 by norm_num))
      _ ≤ q⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hq hqz
  · have he : 162 * (1200 * K * (2 * K / q⁻¹) ^ 4) * (2 * K) ^ 4 * (z⁻¹) ^ 10 =
        49766400 * K ^ 9 * q ^ 4 / z ^ 10 := by
      simp only [div_eq_mul_inv, inv_inv, ← inv_pow]
      ring
    rw [he]
    calc
      _ ≤ 49766400 * K ^ 9 * (K * z) ^ 4 / z ^ 10 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hzpos.le _)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq.le horizon 4) (by positivity)
      _ = (49766400 * K ^ 13) / z ^ 6 := by field_simp
      _ ≤ z / z ^ 6 := div_le_div_of_nonneg_right hbudget (pow_nonneg hzpos.le _)
      _ = 1 / z ^ 5 := by field_simp
      _ ≤ z⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hzpos
          (show z ≤ z ^ 5 by simpa only [pow_one] using pow_le_pow_right₀ hz (show 1 ≤ 5 by norm_num))

theorem scalar_fine_power_mesh_budget (N K q r : ℝ) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hq : 0 < q) (hr : 0 < r) (horizon : q ≤ K * N ^ r)
    (hbudget : 49766400 * K ^ 13 ≤ N ^ r) :
    N ^ (-(10 * r)) ≤ q⁻¹ ∧
      162 * (1200 * K * (2 * K / q⁻¹) ^ 4) * (2 * K) ^ 4 * N ^ (-(10 * r)) ≤ N ^ (-r) := by
  have hN₀ : 0 ≤ N := zero_le_one.trans hN
  have hx := scalar_fine_mesh_budget K (N ^ r) q hK (Real.one_le_rpow hN hr.le) hq horizon hbudget
  have heξ : (N ^ r)⁻¹ = N ^ (-r) := (Real.rpow_neg hN₀ r).symm
  have heδ : ((N ^ r)⁻¹) ^ 10 = N ^ (-(10 * r)) := by
    rw [heξ, ← Real.rpow_natCast (N ^ (-r)) 10, ← Real.rpow_mul hN₀]
    congr 1
    norm_num
    ring
  rwa [heδ, heξ] at hx

theorem scalar_angular_packet_cost_le (K : ℝ) (hK : 1 ≤ K) :
    1600 * (8 * K + 2) * (4 * K + 4) * K ^ 3 ≤ 128000 * K ^ 5 := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  calc
    _ ≤ 1600 * (10 * K) * (8 * K) * K ^ 3 := by gcongr <;> linarith
    _ = _ := by ring

theorem scalar_finite_grid_exception_budget (K J A : ℝ) (hK : 1 ≤ K) (hJ : 0 ≤ J)
    (hA : 0 < A) (hbudget : 12800000 * J ^ 3 * K ^ 6 ≤ A) :
    J ^ 3 * (1600 * (8 * K + 2) * (4 * K + 4) * K ^ 3) / A ≤ 1 / (100 * K) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  apply (div_le_div_iff₀ hA (by positivity : 0 < 100 * K)).mpr
  calc
    _ ≤ (J ^ 3 * (128000 * K ^ 5)) * (100 * K) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (scalar_angular_packet_cost_le K hK) (pow_nonneg hJ _))
        (by positivity)
    _ = 12800000 * J ^ 3 * K ^ 6 := by ring
    _ ≤ 1 * A := by simpa only [one_mul] using hbudget

theorem scalar_scale_support_cost_le (K C C' β : ℝ) (hK : 1 ≤ K)
    (hC : 1 ≤ C) (hC' : 1 ≤ C') (hβ : 0 < β) (hβ₁ : β ≤ 1) :
    4 * K ^ 3 * (8 * K + 2) *
      (4 * (C' * K ^ 2 + (K + 1) * ((max C C' * K ^ 2 + 1 + K) / β) + K) + 2) ≤
        720 * (C + C' + 10) * K ^ 7 / β := by
  let B := C + C' + 10
  let M := (max C C' * K ^ 2 + 1 + K) / β
  let T := B * K ^ 3 / β
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hK23 : K ^ 2 ≤ K ^ 3 := pow_le_pow_right₀ hK (show 2 ≤ 3 by norm_num)
  have hdiv (x : ℝ) (hx : 0 ≤ x) : x ≤ x / β := by
    apply (le_div_iff₀ hβ).mpr
    exact mul_le_of_le_one_right hx hβ₁
  have hT : 1 ≤ T := by
    exact (one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hK)).trans (hdiv _ (by positivity))
  have hmax : max C C' ≤ B - 2 := max_le (by dsimp [B]; linarith) (by dsimp [B]; linarith)
  have hMbound : M ≤ B * K ^ 2 / β := by
    apply div_le_div_of_nonneg_right _ hβ.le
    have hm := mul_le_mul_of_nonneg_right hmax (sq_nonneg K)
    have hone : 1 ≤ K ^ 2 := one_le_pow₀ hK
    nlinarith
  have hCK : C' * K ^ 2 ≤ T := by
    calc
      _ ≤ B * K ^ 2 := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (sq_nonneg K)
      _ ≤ B * K ^ 3 := mul_le_mul_of_nonneg_left hK23 hB₀
      _ ≤ T := hdiv _ (by positivity)
  have hKT : K ≤ T := by
    calc
      _ ≤ K ^ 3 := hK2.trans hK23
      _ ≤ B * K ^ 3 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (by positivity : 0 ≤ K ^ 3)
      _ ≤ T := hdiv _ (by positivity)
  have hKM : (K + 1) * M ≤ 2 * T := by
    calc
      _ ≤ (2 * K) * (B * K ^ 2 / β) :=
        mul_le_mul (by linarith) hMbound hM (by positivity)
      _ = _ := by dsimp [T]; ring
  have hlast : 4 * (C' * K ^ 2 + (K + 1) * M + K) + 2 ≤ 18 * T := by linarith
  have hfirst : 8 * K + 2 ≤ 10 * K := by linarith
  change 4 * K ^ 3 * (8 * K + 2) * (4 * (C' * K ^ 2 + (K + 1) * M + K) + 2) ≤ _
  calc
    _ ≤ 4 * K ^ 3 * (10 * K) * (18 * T) := by gcongr
    _ = _ := by dsimp [T, B]; ring

end Submission.Obl.k4_scalar_grid_parameter_preparation
