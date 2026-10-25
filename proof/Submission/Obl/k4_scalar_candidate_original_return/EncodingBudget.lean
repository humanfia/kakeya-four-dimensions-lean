import Submission.Obl.k4_scalar_candidate_original_return.RecordSupport

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

/-- A fixed natural degree budget is itself bounded by the corresponding
power of any original resolution at least two. -/
lemma nat_budget_le_power {N : ℝ} (hN : 2 ≤ N) (B : ℕ) : (B : ℝ) ≤ N ^ B := by
  calc
    _ ≤ N ^ B / (N - 1) := Nat.cast_le_pow_div_sub (by linarith) B
    _ ≤ N ^ B := div_le_self (by positivity) (by linarith)

lemma source_mesh_denominator (N : ℝ) (M B : ℕ) :
    (N ^ M) ^ 8 * (N ^ B) ^ 3 * N ^ 30 = N ^ (8 * M + 3 * B + 30) := by
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  omega

/-- With the displayed polynomial mesh exponent, summing all scalar source
errors and paying the two list-recovery charges costs at most 1/N. -/
lemma scalar_recovery_mesh_error {N U V : ℝ} (hN : 2 ≤ N) (hU : 0 < U) (hV : 0 < V)
    (B : ℕ) (hB : (B : ℝ) ≤ V) :
    2 * V * (16 * U ^ 2 * (2 * U * V) * (3 * (B : ℝ)) *
      ((U ^ 8 * V ^ 3 * N ^ 30)⁻¹) * (2 * (3 * U)) ^ 5) ≤ N⁻¹ := by
  have hN0 : 0 < N := by linarith
  calc
    _ ≤ 2 * V * (16 * U ^ 2 * (2 * U * V) * (3 * V) *
        ((U ^ 8 * V ^ 3 * N ^ 30)⁻¹) * (2 * (3 * U)) ^ 5) := by gcongr
    _ = 1492992 / N ^ 30 := by
      field_simp
      ring
    _ ≤ N⁻¹ := by
      have hC : (1492992 : ℝ) ≤ N ^ 29 := by
        calc
          _ ≤ (2 : ℝ) ^ 29 := by norm_num
          _ ≤ N ^ 29 := pow_le_pow_left₀ (by norm_num) hN 29
      rw [← one_div]
      apply (div_le_div_iff₀ (pow_pos hN0 30) hN0).mpr
      simpa only [one_mul, pow_succ] using mul_le_mul_of_nonneg_right hC hN0.le

/-- The actual finite scalar observer lookup has an original polynomial
format exponent linear in the prior budget and inverse mesh exponent. -/
lemma original_lookup_format_budget {N δ : ℝ} (hN : 2 ≤ N) (hδ : 0 < δ)
    (M J : ℕ) (hδfine : δ⁻¹ ≤ N ^ J) :
    6 * ((originalRecordCodes (3 * N ^ M) ((N ^ J)⁻¹) δ).card : ℝ) + 1 ≤
      N ^ (3 * (M + J) + 12) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hp : 1 ≤ N ^ (M + J) := one_le_pow₀ hN1
  have hρ : 0 < (N ^ J)⁻¹ := inv_pos.mpr (pow_pos hN0 J)
  have hmax : max ((3 * N ^ M) / (N ^ J)⁻¹) ((3 * N ^ M) / δ) ≤ 3 * N ^ (M + J) := by
    apply max_le
    · rw [div_inv_eq_mul, pow_add]
      ring_nf
      exact le_rfl
    · rw [div_eq_mul_inv, pow_add]
      calc
        _ ≤ (3 * N ^ M) * N ^ J :=
          mul_le_mul_of_nonneg_left hδfine (by positivity)
        _ = _ := by ring
  have hcard : ((originalRecordCodes (3 * N ^ M) ((N ^ J)⁻¹) δ).card : ℝ) ≤
      512 * N ^ (3 * (M + J)) := by
    calc
      _ ≤ (2 * max ((3 * N ^ M) / (N ^ J)⁻¹) ((3 * N ^ M) / δ) + 2) ^ 3 :=
        originalRecordCodes_card (by positivity) hρ hδ
      _ ≤ (8 * N ^ (M + J)) ^ 3 := by gcongr; linarith
      _ = _ := by
        rw [mul_pow, ← pow_mul]
        norm_num
        congr 1
        omega
  have hpower : 1 ≤ N ^ (3 * (M + J)) := one_le_pow₀ hN1
  calc
    _ ≤ 4096 * N ^ (3 * (M + J)) := by linarith
    _ ≤ N ^ 12 * N ^ (3 * (M + J)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 12
      norm_num at hh
      exact hh
    _ = _ := by rw [pow_add]; ring

end Submission.Obl.k4_scalar_candidate_original_return
