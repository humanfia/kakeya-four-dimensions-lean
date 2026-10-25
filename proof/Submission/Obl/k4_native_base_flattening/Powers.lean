import Submission.Obl.k4_real_conic_restoration.Coordinates

namespace Submission.Obl.k4_native_base_flattening

/-- A single integer mesh exponent gives an arbitrary prescribed inverse-power error,
uniformly for every resolution at least two. -/
theorem exists_uniform_mesh_exponent (M : ℕ) (A : ℝ) (q : ℕ) :
    ∃ H : ℕ, ∀ n : ℝ, 2 ≤ n →
      A * (n ^ M) ^ 9 * (n ^ H)⁻¹ ≤ (n ^ q)⁻¹ ∧ (n ^ H)⁻¹ ≤ 1 := by
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt A (by norm_num : (1 : ℝ) < 2)
  refine ⟨M * 9 + a + q, ?_⟩
  intro n hn
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  constructor
  · have hb : A * n ^ (M * 9) ≤ n ^ (M * 9 + a) :=
      Submission.Obl.k4_real_conic_restoration.absorb_constant hn ha.le
    calc
      A * (n ^ M) ^ 9 * (n ^ (M * 9 + a + q))⁻¹ =
          (A * n ^ (M * 9)) / n ^ (M * 9 + a + q) := by rw [pow_mul, div_eq_mul_inv]
      _ ≤ n ^ (M * 9 + a) / n ^ (M * 9 + a + q) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = (n ^ q)⁻¹ := by
        rw [pow_add]
        field_simp
        simp [pow_add]
  · exact (inv_le_one₀ (pow_pos hn0 _)).2 (one_le_pow₀ hn1)

end Submission.Obl.k4_native_base_flattening
