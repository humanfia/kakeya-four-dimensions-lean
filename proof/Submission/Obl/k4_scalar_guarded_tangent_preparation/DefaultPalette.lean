import Submission.Obl.k4_row_cell_regularization.Palette

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set

/-- A fixed probability palette for a parent carrying no retained incidence. -/
noncomputable def unitPalette : Measure ℝ := volume.restrict (Ico 0 1)

theorem unitPalette_probability : IsProbabilityMeasure unitPalette := by
  constructor
  simp [unitPalette]

theorem unitPalette_bin_cap {a : ℝ} (ha : 0 < a) (e : ℤ) :
    unitPalette {v | (⌊v / a⌋ : ℤ) = e} ≤ ENNReal.ofReal a := by
  rw [← Submission.Obl.k4_row_cell_regularization.velocityCell_eq_floor ha]
  calc
    _ ≤ volume (Submission.Obl.k4_row_cell_regularization.velocityCell a e) :=
      Measure.restrict_le_self _
    _ = _ := by
      rw [Submission.Obl.k4_row_cell_regularization.velocityCell, Real.volume_Ico]
      congr 1
      ring

/-- The unused-parent palette satisfies every scalar Frostman exponent
at most one on all positive depths, with no change to the parent law. -/
theorem unitPalette_rpow_cap {N S b : ℝ} (hN : 1 ≤ N) (hS : S ≤ 1) (hb : 0 ≤ b) (e : ℤ) :
    unitPalette {v | (⌊v / (N ^ (-b))⌋ : ℤ) = e} ≤
      ENNReal.ofReal (N ^ (-S * b)) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  apply (unitPalette_bin_cap (Real.rpow_pos_of_pos hNpos _) e).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hN
  nlinarith

end Submission.Obl.k4_scalar_guarded_tangent_preparation
