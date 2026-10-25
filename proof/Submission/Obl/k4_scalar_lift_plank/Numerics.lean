import Submission.Obl.k4_scalar_lift_plank.Cells

namespace Submission.Obl.k4_scalar_lift_plank

/-- One small exponent pays for the two dummy-coordinate counting losses. -/
theorem liftedCells_budget {N η η' c d : ℝ} (hN : 2 ≤ N)
    (hc : 0 < c) (hη : 0 < η) (hη' : 4 * η ≤ η')
    (hlarge : 1000 ≤ N ^ η) (F : Finset (ℤ × ℤ))
    (hF : (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d)) :
    ((liftedCells (N ^ (-c)) (2 * N ^ η) F).card : ℝ) ≤
      N ^ η' * (N ^ (-c)) ^ (-2 - d) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hp : 0 < N ^ (-c) := Real.rpow_pos_of_pos hN0 _
  have hp1 : N ^ (-c) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hM : 0 ≤ N ^ η := (Real.rpow_pos_of_pos hN0 _).le
  have hMp : 1 ≤ 2 * N ^ η := by linarith
  have hr : (N ^ (-c)) ^ (-1 - d) / (N ^ (-c)) = (N ^ (-c)) ^ (-2 - d) := by
    rw [← Real.rpow_sub_one hp.ne']
    congr 1
    ring
  calc
    _ ≤ 200 * (F.card : ℝ) * (2 * N ^ η) ^ 2 / (N ^ (-c)) :=
      card_liftedCells_le hp hp1 hMp F
    _ ≤ 200 * (N ^ η * (N ^ (-c)) ^ (-1 - d)) * (2 * N ^ η) ^ 2 /
        (N ^ (-c)) := by gcongr
    _ = 800 * (N ^ η) ^ 3 * (N ^ (-c)) ^ (-2 - d) := by rw [← hr]; ring
    _ ≤ (N ^ η) ^ 4 * (N ^ (-c)) ^ (-2 - d) := by
      gcongr
      calc
        _ ≤ (N ^ η) * (N ^ η) ^ 3 := by
          apply mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hM _)
        _ = (N ^ η) ^ 4 := by ring
    _ = N ^ (4 * η) * (N ^ (-c)) ^ (-2 - d) := by
      rw [show 4 * η = η * (4 : ℕ) by norm_num; ring, Real.rpow_mul_natCast hN0.le]
    _ ≤ N ^ η' * (N ^ (-c)) ^ (-2 - d) := by
      gcongr

end Submission.Obl.k4_scalar_lift_plank
