import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.Model
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.Background
import Submission.Lib.K4ChartLifting.PolyAlgebra

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set

noncomputable section

namespace Data.ListFrame

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {r v m ε : ℝ}
    (f : ListFrame cfg k r v m ε)

/-- The normalized scalar velocity is the original horizontal velocity
translated by the fixed frame velocity. -/
theorem velocity_eq (l : α) (hl : l ∈ f.good) : f.coeff l 1 = cfg.b k l 3 - f.zv := by
  have h₀ := f.scalarY_eq l hl 0
  have h₁ := f.scalarY_eq l hl 1
  simp only [scalarY, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarY,
    Submission.Obl.k4_critical_conditional_row_preparation.Data.x,
    zero_mul, mul_zero, mul_one, one_mul, add_zero,
    Matrix.cons_val_one, Matrix.cons_val_zero] at h₀ h₁
  have h₀ := (eq_div_iff f.q_pos.ne').mp h₀
  have h₁ := (eq_div_iff f.q_pos.ne').mp h₁
  apply mul_right_cancel₀ f.q_pos.ne'
  calc
    f.coeff l 1 * f.q = (f.coeff l 0 + f.coeff l 1) * f.q - f.coeff l 0 * f.q := by ring
    _ = (cfg.b k l 3 - f.zv) * f.q := by rw [h₀, h₁]; ring

theorem q_le_one : f.q ≤ 1 := by
  rw [f.q_eq]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem background_coeff_bound (e : Fin 3 →₀ ℕ) :
    |f.background.coeff e| ≤ cfg.N k ^ (m / 10) := by
  exact (Submission.Lib.K4ChartLifting.abs_coeff_le_coeffL1 f.background e).trans
    f.background_bound

theorem unit_time_mem (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    f.t₀ + f.q * u ∈ Submission.Obl.k4_critical_conditional_row_preparation.Data.I
      (cfg.T k r) (cfg.j k r f.parent) := by
  rw [f.time_eq]
  exact ⟨by linarith [mul_nonneg f.q_pos.le hu.1],
    by linarith [mul_le_mul_of_nonneg_left hu.2 f.q_pos.le]⟩

/-- Every component of the frame is controlled by its stated fixed budget. -/
theorem frame_component_bounds :
    f.q⁻¹ ≤ cfg.N k ^ (m / 10) ∧ |f.zv| ≤ cfg.N k ^ (m / 10) := by
  have hqi : 1 ≤ f.q⁻¹ := (one_le_inv₀ f.q_pos).mpr f.q_le_one
  have hqi0 : 0 ≤ f.q⁻¹ := inv_nonneg.mpr f.q_pos.le
  have hB := f.frame_bound
  rw [abs_of_pos (inv_pos.mpr f.q_pos)] at hB
  have hz : |f.zv| ≤ f.q⁻¹ * |f.zv| := le_mul_of_one_le_left (abs_nonneg _) hqi
  have hlarge : f.q⁻¹ * |f.zv| ≤
      f.q⁻¹ * (2 + |f.t₀| + |f.z₀| + |f.zv|) := by
    apply mul_le_mul_of_nonneg_left _ hqi0
    linarith [abs_nonneg f.t₀, abs_nonneg f.z₀]
  have hlarge' : 2 * f.q⁻¹ ≤
      f.q⁻¹ * (2 + |f.t₀| + |f.z₀| + |f.zv|) := by
    have hh : 2 ≤ 2 + |f.t₀| + |f.z₀| + |f.zv| := by
      linarith [abs_nonneg f.t₀, abs_nonneg f.z₀, abs_nonneg f.zv]
    nlinarith [mul_le_mul_of_nonneg_left hh hqi0]
  constructor <;> linarith

end Data.ListFrame

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
