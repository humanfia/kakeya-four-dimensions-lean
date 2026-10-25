import Submission.Obl.k4_real_conic_restoration.Basic

set_option linter.unusedVariables false

namespace Submission.Obl.k4_real_conic_restoration

/-- A quadratic with small residual and a nonzero linear term has a nearby real zero. -/
theorem quadratic_near_zero (a b c : ℝ) (hb : b ≠ 0)
    (hsmall : 4 * |a| * |c| ≤ b ^ 2) :
    ∃ t : ℝ, c + b * t + a * t ^ 2 = 0 ∧ |t| ≤ 2 * |c| / |b| := by
  let f : ℝ → ℝ := fun t => c + b * t + a * t ^ 2
  let s : ℝ := -2 * c / b
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hac : 4 * a * c ≤ b ^ 2 := by
    have h := le_abs_self (a * c)
    rw [abs_mul] at h
    nlinarith
  have hid : c * f s * b ^ 2 = c ^ 2 * (4 * a * c - b ^ 2) := by
    dsimp [f, s]
    field_simp
    ring
  have hprod : c * f s ≤ 0 := by
    have hright : c ^ 2 * (4 * a * c - b ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
    nlinarith
  have hzero : 0 ∈ Set.uIcc (f 0) (f s) := by
    simp only [f, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at *
    rcases mul_nonpos_iff.mp hprod with h | h
    · exact Set.mem_uIcc.mpr (Or.inr ⟨h.2, h.1⟩)
    · exact Set.mem_uIcc.mpr (Or.inl ⟨h.1, h.2⟩)
  have hf : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨t, ht, hft⟩ := intermediate_value_uIcc hf.continuousOn hzero
  refine ⟨t, hft, ?_⟩
  have ht' : |t| ≤ |s| := by
    rcases Set.mem_uIcc.mp ht with h | h
    · simpa only [abs_zero, max_eq_right (abs_nonneg s)] using abs_le_max_abs_abs h.1 h.2
    · simpa only [abs_zero, max_eq_left (abs_nonneg s)] using abs_le_max_abs_abs h.1 h.2
  calc
    |t| ≤ |s| := ht'
    _ = 2 * |c| / |b| := by simp only [s, abs_div, abs_mul]; norm_num

end Submission.Obl.k4_real_conic_restoration
