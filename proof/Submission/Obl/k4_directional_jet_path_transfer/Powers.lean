import Submission.Obl.k4_directional_jet_path_transfer.Cauchy

open Metric Set

namespace Submission.Obl.k4_directional_jet_path_transfer

/-- A fixed constant and a fixed power are dominated by one positive power on `A ≥ 2`. -/
lemma exists_power_bound (C d : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ A : ℝ, 2 ≤ A → C * A ^ d ≤ A ^ L := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  refine ⟨(m : ℝ) + max d 0 + 1, by positivity, ?_⟩
  intro A hA
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  calc
    C * A ^ d ≤ (2 : ℝ) ^ m * A ^ d := mul_le_mul_of_nonneg_right hm.le (Real.rpow_nonneg hA0.le _)
    _ ≤ A ^ m * A ^ d := by gcongr
    _ = A ^ ((m : ℝ) + d) := by rw [Real.rpow_add hA0, Real.rpow_natCast]
    _ ≤ A ^ ((m : ℝ) + max d 0 + 1) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (by linarith [le_max_left d 0])

/-- All Cauchy factors through a prescribed order fit in a single power of `A`. -/
lemma exists_cauchy_power (q : ℕ) :
    ∃ J : ℝ, 0 < J ∧ ∀ A : ℝ, 2 ≤ A → ∀ j : ℕ, j ≤ q →
      cauchyConstant j * (8 * A) ^ j ≤ A ^ J := by
  let C : ℝ := ∑ j ∈ Finset.range (q + 1), cauchyConstant j * 8 ^ j
  obtain ⟨J, hJ, hbound⟩ := exists_power_bound C (q : ℝ)
  refine ⟨J, hJ, ?_⟩
  intro A hA j hj
  have hA0 : 0 ≤ A := by linarith
  have hAj : A ^ j ≤ A ^ q := pow_le_pow_right₀ (by linarith) hj
  have hCj : cauchyConstant j * 8 ^ j ≤ C := by
    apply Finset.single_le_sum (f := fun i => cauchyConstant i * (8 : ℝ) ^ i)
    · intro i hi
      exact mul_nonneg (cauchyConstant_pos i).le (by positivity)
    · exact Finset.mem_range.mpr (by omega)
  calc
    cauchyConstant j * (8 * A) ^ j = (cauchyConstant j * 8 ^ j) * A ^ j := by rw [mul_pow]; ring
    _ ≤ C * A ^ q := mul_le_mul hCj hAj (by positivity) (le_trans (mul_nonneg (cauchyConstant_pos j).le (by positivity)) hCj)
    _ = C * A ^ (q : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ A ^ J := hbound A hA

lemma exists_slice_power (N : ℕ) (K : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ A : ℝ, 2 ≤ A →
      (8 * A) ^ K * (3 : ℝ) ^ N ≤ A ^ D := by
  obtain ⟨D, hD, hb⟩ := exists_power_bound ((8 : ℝ) ^ K * (3 : ℝ) ^ N) K
  refine ⟨D, hD, ?_⟩
  intro A hA
  convert hb A hA using 1
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (by linarith : 0 ≤ A)]
  ring

end Submission.Obl.k4_directional_jet_path_transfer
