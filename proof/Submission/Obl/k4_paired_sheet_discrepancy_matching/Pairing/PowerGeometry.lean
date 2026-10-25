/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/PowerGeometry.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.MatchingScales

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.MatchingScales

variable {d₀ ε₀ : ℝ} (p : MatchingScales d₀ ε₀)

theorem output_floor {X : ℝ} (hX : 1 ≤ X) : X ^ (-p.output) ≤ X ^ (-1 : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hX
  have := p.size_one
  dsimp [output]
  linarith

theorem output_radius {X : ℝ} (hX : 4 ≤ X) :
    2 * X ^ (-p.output) ≤ X ^ (-3 : ℝ) / 2 := by
  have hXpos : 0 < X := by linarith
  have hp : X ^ (-p.output) ≤ X ^ (-4 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have := p.size_one
    dsimp [output]
    linarith
  have hstep : X ^ (-4 : ℝ) = X ^ (-3 : ℝ) / X := by
    have := Real.rpow_sub hXpos (-3) 1
    simpa only [show (-3 : ℝ) - 1 = -4 by norm_num, Real.rpow_one] using this
  calc _ ≤ 2 * X ^ (-4 : ℝ) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 2 * (X ^ (-3 : ℝ) / X) := by rw [hstep]
    _ ≤ 2 * (X ^ (-3 : ℝ) / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hXpos.le _) (by norm_num) hX
    _ = _ := by ring

theorem output_error {X : ℝ} (hX : 4 ≤ X) : 4 * X ^ 2 ≤ X ^ p.output := by
  have hXpos : 0 < X := by linarith
  calc _ ≤ X * X ^ 2 := mul_le_mul_of_nonneg_right hX (sq_nonneg X)
    _ = X ^ (3 : ℝ) := by
      calc _ = X ^ (1 : ℝ) * X ^ (2 : ℝ) := by simp only [Real.rpow_one, Real.rpow_two]
        _ = X ^ ((1 : ℝ) + 2) := (Real.rpow_add hXpos _ _).symm
        _ = _ := by norm_num
    _ ≤ X ^ p.output := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      have := p.size_one
      dsimp [output]
      linarith

theorem output_slope {X : ℝ} (hX : 1 ≤ X) :
    2 * X * (X ^ (-p.output) / 100) ≤ X ^ (-1 : ℝ) / 2 := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hp : X * X ^ (-p.output) ≤ X ^ (-1 : ℝ) := by
    calc _ = X ^ (1 : ℝ) * X ^ (-p.output) := by rw [Real.rpow_one]
      _ = X ^ (1 + -p.output) := (Real.rpow_add hXpos _ _).symm
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hX
        have := p.size_one
        dsimp [output]
        linarith
  calc _ = (2 / 100 : ℝ) * (X * X ^ (-p.output)) := by ring
    _ ≤ (2 / 100 : ℝ) * X ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ _ := by have := Real.rpow_nonneg hXpos.le (-1); linarith

theorem band_amplitude {X : ℝ} (hX : 8 ≤ X) :
    8 * X ^ 2 * X ^ p.size ≤ X ^ (p.size + 3) := by
  have hXpos : 0 < X := by linarith
  calc _ ≤ X * X ^ 2 * X ^ p.size := by gcongr
    _ = X ^ (p.size + 3) := by
      calc _ = (X ^ (1 : ℝ) * X ^ (2 : ℝ)) * X ^ p.size := by
                simp only [Real.rpow_one, Real.rpow_two]
        _ = X ^ (1 + 2 + p.size) := by rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
        _ = _ := by congr 1; ring

theorem threshold_output {X δ : ℝ} (hX : 8 ≤ X) (hδ : 0 ≤ δ) :
    4 * δ * X ^ 2 * X ^ p.size ≤ δ * X ^ p.output := by
  have hXpos : 0 < X := by linarith
  have hmul : X ^ (p.size + 3) ≤ X ^ p.output := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    dsimp [output]
    linarith
  calc _ ≤ δ * (8 * X ^ 2 * X ^ p.size) := by
          have := Real.rpow_nonneg hXpos.le p.size
          nlinarith [mul_nonneg hδ (mul_nonneg (sq_nonneg X) this)]
    _ ≤ δ * X ^ (p.size + 3) := mul_le_mul_of_nonneg_left (p.band_amplitude hX) hδ
    _ ≤ _ := mul_le_mul_of_nonneg_left hmul hδ

theorem grid_radius_small {X : ℝ} (hX : 4 ≤ X) : X ^ (-3 : ℝ) ≤ 1 / 16 := by
  have hXpos : 0 < X := by linarith
  calc _ ≤ X ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = (X ^ 2)⁻¹ := by rw [Real.rpow_neg hXpos.le, Real.rpow_two]
    _ ≤ (16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith)
    _ = _ := by norm_num

theorem grid_positive_margin {X C : ℝ} (hX : 0 < X) (hCX : 9 * C < X) :
    9 * C * X * X ^ (-3 : ℝ) < X ^ (-1 : ℝ) := by
  have hcancel : X * X ^ (-3 : ℝ) = X ^ (-2 : ℝ) := by
    calc _ = X ^ (1 : ℝ) * X ^ (-3 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hX]; norm_num
  have hcancel' : X * X ^ (-2 : ℝ) = X ^ (-1 : ℝ) := by
    calc _ = X ^ (1 : ℝ) * X ^ (-2 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hX]; norm_num
  calc _ = 9 * C * X ^ (-2 : ℝ) := by rw [mul_assoc, hcancel]
    _ < X * X ^ (-2 : ℝ) := mul_lt_mul_of_pos_right hCX (Real.rpow_pos_of_pos hX _)
    _ = _ := hcancel'

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.MatchingScales
