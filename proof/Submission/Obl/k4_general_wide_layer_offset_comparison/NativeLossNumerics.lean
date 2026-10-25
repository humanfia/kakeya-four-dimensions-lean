import Submission.Obl.k4_general_wide_layer_offset_comparison.Confine.Numerics

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/NativeLossNumerics.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

/-- The accepted full-parent filling constant dominates both factors of
the two-pass native-sheet construction, including its native-bin ceiling. -/
theorem parent_filling_two_pass_bounds {M a : ℝ} (hM : 1 ≤ M) (ha : 0 < a) (ha1 : a ≤ 1) :
    2 * M ≤ parentFilling M a ∧ 442368 * M ^ 6 ≤ parentFilling M a ∧
      (parentFilling M a)⁻¹ ≤ a := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have h20 : M ≤ M ^ 20 := le_self_pow₀ hM (by norm_num)
  have h620 : M ^ 6 ≤ M ^ 20 := pow_le_pow_right₀ hM (by norm_num)
  have hraw : 1 ≤ 3000000 * M ^ 20 := by
    have hh : 1 ≤ M ^ 20 := one_le_pow₀ hM
    nlinarith
  have hfill : 3000000 * M ^ 20 ≤ parentFilling M a := by
    unfold parentFilling
    exact (le_div_iff₀ ha).mpr (mul_le_of_le_one_right (by positivity) ha1)
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ 3000000 * M := mul_le_mul_of_nonneg_right (by norm_num) hM0
      _ ≤ 3000000 * M ^ 20 := mul_le_mul_of_nonneg_left h20 (by norm_num)
      _ ≤ _ := hfill
  · calc
      _ ≤ 3000000 * M ^ 6 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hM0 _)
      _ ≤ 3000000 * M ^ 20 := mul_le_mul_of_nonneg_left h620 (by norm_num)
      _ ≤ _ := hfill
  · unfold parentFilling
    rw [inv_div]
    exact div_le_self ha.le hraw

/-- One physical mesh, resolved at the filling power 2n+1, satisfies BOTH
passes. Its exponent stays fixed while the parent loss varies with k. -/
theorem two_pass_mesh_of_filling {M F B a σ : ℝ} (hM : 1 ≤ M)
    (hF : 2 * M ≤ F) (hB : 1 ≤ B) (hBF : B ≤ F)
    (ha : F⁻¹ ≤ a) (ha1 : a ≤ 1) (hσ : 0 ≤ σ) (n : ℕ)
    (hres : σ ≤ (F ^ (2 * n + 1))⁻¹) :
    (2 * M * F) ^ n * σ ≤ a ∧ (2 * M * B) ^ n * σ ≤ 1 := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hFp : 0 < F := (by linarith : 0 < 2 * M).trans_le hF
  have hbase : 2 * M * F ≤ F ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hF hFp.le
  have hp : (2 * M * F) ^ n ≤ F ^ (2 * n) := by
    simpa only [pow_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ 2 * M * F) hbase n
  have hfirst : (2 * M * F) ^ n * σ ≤ a := by
    calc
      _ ≤ F ^ (2 * n) * (F ^ (2 * n + 1))⁻¹ :=
        mul_le_mul hp hres hσ (pow_nonneg hFp.le _)
      _ = F⁻¹ := by
        rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hFp.ne'), one_mul]
      _ ≤ _ := ha
  refine ⟨hfirst, ?_⟩
  have hsmall : 2 * M * B ≤ 2 * M * F := mul_le_mul_of_nonneg_left hBF (by positivity)
  exact ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : 0 ≤ 2 * M * B) hsmall n) hσ).trans hfirst).trans ha1

/-- Summing the relative native-sheet exceptions over every original
true parent still leaves an inverse power of the enlarged parent loss. -/
theorem two_pass_original_exception {M F B : ℝ}
    (hM : 1 ≤ M) (hF : 1 ≤ F) (hB : 1 ≤ B) {A : ℕ} (hA : 1 ≤ A) :
    M * (((2 * M * F) ^ A)⁻¹ + ((2 * M * B) ^ A)⁻¹) ≤ M / M ^ A := by
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have h2Mp : 0 < 2 * M := by positivity
  have hFpow : (2 * M) ^ A ≤ (2 * M * F) ^ A :=
    pow_le_pow_left₀ h2Mp.le (le_mul_of_one_le_right h2Mp.le hF) _
  have hBpow : (2 * M) ^ A ≤ (2 * M * B) ^ A :=
    pow_le_pow_left₀ h2Mp.le (le_mul_of_one_le_right h2Mp.le hB) _
  have htwo : (2 : ℝ) ≤ 2 ^ A := le_self_pow₀ (by norm_num) (by omega)
  have hratio : 2 * ((2 * M) ^ A)⁻¹ ≤ (M ^ A)⁻¹ := by
    rw [← div_eq_mul_inv, ← one_div (M ^ A)]
    apply (div_le_div_iff₀ (pow_pos h2Mp _) (pow_pos hMp _)).mpr
    rw [mul_pow, one_mul]
    exact mul_le_mul_of_nonneg_right htwo (pow_nonneg hMp.le _)
  calc
    _ ≤ M * (((2 * M) ^ A)⁻¹ + ((2 * M) ^ A)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (inv_anti₀ (pow_pos h2Mp _) hFpow) (inv_anti₀ (pow_pos h2Mp _) hBpow)) hMp.le
    _ = M * (2 * ((2 * M) ^ A)⁻¹) := by ring
    _ ≤ M * (M ^ A)⁻¹ := mul_le_mul_of_nonneg_left hratio hMp.le
    _ = _ := (div_eq_mul_inv _ _).symm

/-- A fixed loss exponent four is enough to reserve three quarters of
an original source of mass at least 1/M. No loss exponent grows with k. -/
theorem two_pass_original_exception_four {M F B : ℝ}
    (hM : 2 ≤ M) (hF : 1 ≤ F) (hB : 1 ≤ B) :
    M * (((2 * M * F) ^ 4)⁻¹ + ((2 * M * B) ^ 4)⁻¹) ≤ (4 * M)⁻¹ := by
  apply (two_pass_original_exception (by linarith : 1 ≤ M) hF hB (by norm_num : 1 ≤ 4)).trans
  have hMp : 0 < M := by linarith
  rw [← one_div (4 * M)]
  apply (div_le_div_iff₀ (pow_pos hMp _) (by positivity : 0 < 4 * M)).mpr
  have hM2 : 4 ≤ M ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg M) (sub_nonneg.mpr hM2)]

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
