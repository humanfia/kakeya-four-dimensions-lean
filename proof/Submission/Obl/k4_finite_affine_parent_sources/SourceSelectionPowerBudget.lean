import Mathlib

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- The appended-state cutoff loses at most one eighth of the retained mass,
including the factor eight from the unchanged parent reference. -/
theorem kept_state_power_loss {A : ℝ} (hA : 10000 ≤ A) (C : ℕ) :
    81 * A ^ (6 * C) * (A ^ (6 * C + 2))⁻¹ * 8 ≤ 1 / 8 := by
  have hA0 : 0 < A := by linarith
  have heq : 81 * A ^ (6 * C) * (A ^ (6 * C + 2))⁻¹ * 8 = 648 / A ^ 2 := by
    rw [pow_add]
    field_simp
    <;> ring
  rw [heq, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (A - 10000)]

/-- A group constant of the sixth budget power has a negligible group loss. -/
theorem group_power_loss {A : ℝ} (hA : 10000 ≤ A) : (A ^ 6)⁻¹ ≤ 1 / 16 := by
  have hpow : 16 ≤ A ^ 6 :=
    (by norm_num : (16 : ℝ) ≤ 10000).trans (hA.trans (le_self_pow₀ (by linarith) (by norm_num)))
  simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 16) hpow

/-- The common cutoff preserves the original palette and pays the joint-cell
constant within a fixed tenth of the final exponent. -/
theorem kept_joint_power_budget {A Cw Cp : ℝ} (hA : 10000 ≤ A) (C : ℕ)
    (hCw : Cw ≤ A) (hCp0 : 0 ≤ Cp) (hCp : Cp ≤ A ^ 4) :
    81 * (4 * Cw / (A ^ (6 * C + 2))⁻¹) * Cp ≤ A ^ (10 * (C + 2)) := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  calc 81 * (4 * Cw / (A ^ (6 * C + 2))⁻¹) * Cp
      = 324 * Cw * A ^ (6 * C + 2) * Cp := by rw [div_inv_eq_mul]; ring
    _ ≤ 324 * A * A ^ (6 * C + 2) * A ^ 4 := by gcongr
    _ = 324 * A ^ (6 * C + 7) := by
      rw [show 6 * C + 7 = 1 + (6 * C + 2) + 4 by omega]
      simp only [pow_add, pow_one]
      ring
    _ ≤ A * A ^ (6 * C + 7) := by gcongr; linarith
    _ = A ^ (6 * C + 8) := by rw [pow_succ]; ring
    _ ≤ _ := pow_le_pow_right₀ hA1 (by omega)

/-- The quadratic raw-coordinate upgrade remains inside the final stage power. -/
theorem kept_raw_power_budget {A : ℝ} (hA : 10000 ≤ A) (C : ℕ) :
    400 * (A ^ (10 * (C + 2))) ^ 2 ≤ A ^ (100 * (C + 2)) := by
  have hA1 : 1 ≤ A := by linarith
  have h400 : 400 ≤ A ^ 2 := by nlinarith [sq_nonneg (A - 10000)]
  calc 400 * (A ^ (10 * (C + 2))) ^ 2 ≤ A ^ 2 * (A ^ (10 * (C + 2))) ^ 2 := by
          gcongr
    _ = A ^ (2 + 2 * (10 * (C + 2))) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ _ := pow_le_pow_right₀ hA1 (by omega)

/-- The group and end-label deletions cost at most a quarter of the positive
window mass, using its original packet floor. -/
theorem window_deletion_power_budget {A m κ P R : ℝ} (hA : 10000 ≤ A)
    (hm : 0 < m) (hκ : 0 < κ) (hR : 0 ≤ R)
    (hcost : 1024 * m * κ ^ 2 ≤ A)
    (hfloor : (1 / (64 * m * κ ^ 2)) * P ≤ R) :
    2 * A⁻¹ * P + (A ^ 6)⁻¹ * R ≤ R / 4 := by
  have hA0 : 0 < A := by linarith
  have hP : P ≤ (64 * m * κ ^ 2) * R := by
    have hf : P / (64 * m * κ ^ 2) ≤ R := by convert hfloor using 1 <;> ring
    exact (div_le_iff₀ (by positivity)).mp hf |>.trans_eq (mul_comm _ _)
  have hcoef : 128 * m * κ ^ 2 / A ≤ 1 / 8 := by
    rw [div_le_iff₀ hA0]
    nlinarith [hcost]
  have hpkt : 2 * A⁻¹ * P ≤ R / 8 := by
    calc 2 * A⁻¹ * P ≤ 2 * A⁻¹ * ((64 * m * κ ^ 2) * R) := by gcongr
      _ = (128 * m * κ ^ 2 / A) * R := by ring
      _ ≤ (1 / 8) * R := mul_le_mul_of_nonneg_right hcoef hR
      _ = _ := by ring
  have hgroup := mul_le_mul_of_nonneg_right (group_power_loss hA) hR
  linarith

end

end Submission.Obl.k4_finite_affine_parent_sources
