import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.Chart

/-!
# Size bounds for the normalized chart

Row sums of the chart matrix and the substitution budget, in terms of the block data.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

noncomputable section

namespace ChartData

variable (D : ChartData)

theorem normMat_entries :
    D.normMat = !![D.q⁻¹, 0, 0; 0, (8 * D.B)⁻¹ * D.q⁻¹, 0;
      -1 / 4 * D.q⁻¹ + (8 * D.B)⁻¹ * (D.Z₀ / D.q ^ 2), (8 * D.B)⁻¹ * (-D.t₀ / D.q ^ 2),
        (8 * D.B)⁻¹ * (D.q ^ 2)⁻¹] := by
  unfold normMat
  ext r m
  fin_cases r <;> fin_cases m <;>
    simp [unitContactMatrix, contactFrameMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem normMat_rowSum_le (hq : 0 < D.q) (hB : 1 ≤ 8 * D.B) (r : Fin 3) :
    ∑ m, |D.normMat r m| ≤ (1 + |D.t₀| + |D.Z₀|) * (D.q⁻¹ + (D.q ^ 2)⁻¹) := by
  have hBi : (8 * D.B)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hB
  have hBi0 : 0 ≤ (8 * D.B)⁻¹ := by positivity
  have hq1 : 0 < D.q⁻¹ := inv_pos.mpr hq
  have hq2 : 0 < (D.q ^ 2)⁻¹ := by positivity
  have ht := abs_nonneg D.t₀
  have hZ := abs_nonneg D.Z₀
  have hM := D.normMat_entries
  have e00 : D.normMat 0 0 = D.q⁻¹ := by rw [hM]; rfl
  have e01 : D.normMat 0 1 = 0 := by rw [hM]; rfl
  have e02 : D.normMat 0 2 = 0 := by rw [hM]; rfl
  have e10 : D.normMat 1 0 = 0 := by rw [hM]; rfl
  have e11 : D.normMat 1 1 = (8 * D.B)⁻¹ * D.q⁻¹ := by rw [hM]; rfl
  have e12 : D.normMat 1 2 = 0 := by rw [hM]; rfl
  have e20 : D.normMat 2 0 = -1 / 4 * D.q⁻¹ + (8 * D.B)⁻¹ * (D.Z₀ / D.q ^ 2) := by rw [hM]; rfl
  have e21 : D.normMat 2 1 = (8 * D.B)⁻¹ * (-D.t₀ / D.q ^ 2) := by rw [hM]; rfl
  have e22 : D.normMat 2 2 = (8 * D.B)⁻¹ * (D.q ^ 2)⁻¹ := by rw [hM]; rfl
  have hprod : D.q⁻¹ + (D.q ^ 2)⁻¹ ≤ (1 + |D.t₀| + |D.Z₀|) * (D.q⁻¹ + (D.q ^ 2)⁻¹) := by
    nlinarith
  rw [Fin.sum_univ_three]
  fin_cases r
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [e00, e01, e02, abs_zero, abs_of_pos hq1]
    linarith
  · simp only [Fin.mk_one, Fin.isValue]
    rw [e10, e11, e12, abs_zero, abs_mul, abs_of_nonneg hBi0, abs_of_pos hq1]
    have := mul_le_mul_of_nonneg_right hBi hq1.le
    linarith
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [e20, e21, e22]
    have a1 : |-1 / 4 * D.q⁻¹| ≤ D.q⁻¹ := by
      rw [abs_mul, abs_of_pos hq1]; norm_num
      linarith
    have a2 : |(8 * D.B)⁻¹ * (D.Z₀ / D.q ^ 2)| ≤ |D.Z₀| * (D.q ^ 2)⁻¹ := by
      rw [abs_mul, abs_of_nonneg hBi0, abs_div, abs_of_pos (by positivity : (0 : ℝ) < D.q ^ 2),
        div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_right hBi (by positivity : 0 ≤ |D.Z₀| * (D.q ^ 2)⁻¹)
      linarith
    have a3 : |(8 * D.B)⁻¹ * (-D.t₀ / D.q ^ 2)| ≤ |D.t₀| * (D.q ^ 2)⁻¹ := by
      rw [abs_mul, abs_of_nonneg hBi0, abs_div, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < D.q ^ 2), div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_right hBi (by positivity : 0 ≤ |D.t₀| * (D.q ^ 2)⁻¹)
      linarith
    have a4 : |(8 * D.B)⁻¹ * (D.q ^ 2)⁻¹| ≤ (D.q ^ 2)⁻¹ := by
      rw [abs_mul, abs_of_nonneg hBi0, abs_of_pos hq2]
      have := mul_le_mul_of_nonneg_right hBi hq2.le
      linarith
    have a0 := abs_add_le (-1 / 4 * D.q⁻¹) ((8 * D.B)⁻¹ * (D.Z₀ / D.q ^ 2))
    have hfin : D.q⁻¹ + |D.Z₀| * (D.q ^ 2)⁻¹ + |D.t₀| * (D.q ^ 2)⁻¹ + (D.q ^ 2)⁻¹ ≤
        (1 + |D.t₀| + |D.Z₀|) * (D.q⁻¹ + (D.q ^ 2)⁻¹) := by nlinarith
    linarith

theorem substBudget_one_le (ht : |D.t₀| ≤ 1) (hq : 0 ≤ D.q) (hq1 : D.q ≤ 1) (hγ : |D.γ| ≤ 9 / 8)
    (hB : 0 ≤ D.B) : D.substBudget 1 ≤ 7 + 4 * |D.Z₀| + |D.Y₀| + 34 * D.B := by
  unfold substBudget
  have hqa : |D.q| ≤ 1 := by rw [abs_of_nonneg hq]; exact hq1
  have h8 : |8 * D.B * D.q| ≤ 8 * D.B := by
    rw [abs_mul, abs_mul, abs_of_nonneg hB]; norm_num
    exact mul_le_of_le_one_right (by positivity) hqa
  have h82 : |8 * D.B * D.q ^ 2| ≤ 8 * D.B := by
    rw [abs_mul, abs_mul, abs_of_nonneg hB, abs_of_nonneg (sq_nonneg D.q)]; norm_num
    exact mul_le_of_le_one_right (by positivity) (by nlinarith)
  have hZ := abs_nonneg D.Z₀
  have hY := abs_nonneg D.Y₀
  have ht0 := abs_nonneg D.t₀
  have hq0 := abs_nonneg D.q
  have h8n := abs_nonneg (8 * D.B * D.q)
  have p1 : |D.Z₀| * (|D.t₀| + |D.q|) ≤ 2 * |D.Z₀| := by nlinarith
  have p2 : |D.t₀| * (|D.Z₀| + |8 * D.B * D.q| * (5 / 4)) ≤ |D.Z₀| + 10 * D.B := by nlinarith
  rw [abs_one]
  nlinarith

end ChartData

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
