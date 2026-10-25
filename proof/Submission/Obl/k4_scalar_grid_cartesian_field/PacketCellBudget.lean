import Mathlib

namespace Submission.Obl.k4_scalar_grid_cartesian_field

/-- The fine physical support count is calibrated to the unchanged full trajectory prior.
Multiplying by the natural `(2+d)`-dimensional cell weight cancels every fine-grid factor. -/
theorem packet_cell_count_budget {A K h δ b d : ℝ} (hA : 0 ≤ A) (hK : 0 < K)
    (hh : 0 ≤ h) (hδ : 0 < δ) (hb : 0 < b) (n : ℕ) (m : ENNReal)
    (hcount : (n : ℝ) ≤ A * (h / b) ^ 2 * (δ / b) ^ d)
    (hfloor : ENNReal.ofReal (δ ^ d * h / K) ≤ m) :
    ENNReal.ofReal (b ^ (2 + d)) * (n : ENNReal) ≤
      ENNReal.ofReal (A * K * h) * m := by
  have hbp : 0 < b ^ (2 + d) := Real.rpow_pos_of_pos hb _
  have hbd : 0 < b ^ d := Real.rpow_pos_of_pos hb _
  have hcancel : b ^ (2 + d) * (h / b) ^ 2 * (δ / b) ^ d = h ^ 2 * δ ^ d := by
    rw [Real.rpow_add hb, Real.rpow_two, Real.div_rpow hδ.le hb.le]
    field_simp
  have hreal : b ^ (2 + d) * (n : ℝ) ≤ (A * K * h) * (δ ^ d * h / K) := by
    calc
      _ ≤ b ^ (2 + d) * (A * (h / b) ^ 2 * (δ / b) ^ d) :=
        mul_le_mul_of_nonneg_left hcount hbp.le
      _ = A * (b ^ (2 + d) * (h / b) ^ 2 * (δ / b) ^ d) := by ring
      _ = A * (h ^ 2 * δ ^ d) := by rw [hcancel]
      _ = _ := by field_simp
  calc
    _ = ENNReal.ofReal (b ^ (2 + d) * (n : ℝ)) := by
      rw [ENNReal.ofReal_mul hbp.le, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((A * K * h) * (δ ^ d * h / K)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (A * K * h) * ENNReal.ofReal (δ ^ d * h / K) :=
      ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := mul_le_mul' le_rfl hfloor

end Submission.Obl.k4_scalar_grid_cartesian_field
