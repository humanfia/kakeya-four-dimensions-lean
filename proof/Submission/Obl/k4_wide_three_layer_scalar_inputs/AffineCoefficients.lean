import Mathlib

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

/-- The calibrated slopes and one occupied bounded sample control all
four affine coefficients, including the otherwise unrestricted constant. -/
theorem affine_coefficients_from_sample (L : Fin 4 → ℝ)
    {t Z Y X H E B : ℝ} (hH : 1 ≤ H) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (ht : |t| ≤ 1) (hZ : |Z| ≤ H) (hY : |Y| ≤ H) (hX : |X| ≤ H)
    (hL3 : |L 3| ≤ B)
    (hslope : |L 1 - Z * L 3| + |L 2 + t * L 3| ≤ B)
    (hfit : |X - (L 0 + L 1 * t + L 2 * Z + L 3 * Y)| ≤ E) :
    ∀ i, |L i| ≤ H + E + 3 * (1 + H) ^ 2 * B := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hs1 : |L 1 - Z * L 3| ≤ B := by linarith [abs_nonneg (L 2 + t * L 3)]
  have hs2 : |L 2 + t * L 3| ≤ B := by linarith [abs_nonneg (L 1 - Z * L 3)]
  have h1 : |L 1| ≤ (1 + H) * B := by
    calc
      _ = |(L 1 - Z * L 3) + Z * L 3| := by congr 1; ring
      _ ≤ |L 1 - Z * L 3| + |Z * L 3| := abs_add_le _ _
      _ ≤ B + H * B := by rw [abs_mul]; gcongr
      _ = _ := by ring
  have h2 : |L 2| ≤ (1 + H) * B := by
    calc
      _ = |(L 2 + t * L 3) - t * L 3| := by congr 1; ring
      _ ≤ |L 2 + t * L 3| + |t * L 3| := abs_sub _ _
      _ ≤ B + 1 * B := by rw [abs_mul]; gcongr
      _ ≤ _ := by nlinarith
  have hbig : (1 + H) * B ≤ 3 * (1 + H) ^ 2 * B := by
    gcongr
    nlinarith [sq_nonneg H]
  have h0 : |L 0| ≤ H + E + 3 * (1 + H) ^ 2 * B := by
    have hid : L 0 = X - (X - (L 0 + L 1 * t + L 2 * Z + L 3 * Y)) -
        L 1 * t - L 2 * Z - L 3 * Y := by ring
    calc
      _ = |X - (X - (L 0 + L 1 * t + L 2 * Z + L 3 * Y)) -
          L 1 * t - L 2 * Z - L 3 * Y| := congrArg abs hid
      _ ≤ |X| + |X - (L 0 + L 1 * t + L 2 * Z + L 3 * Y)| +
          |L 1 * t| + |L 2 * Z| + |L 3 * Y| := by
        grw [abs_sub, abs_sub, abs_sub, abs_sub]
      _ ≤ H + E + ((1 + H) * B) * 1 + ((1 + H) * B) * H + B * H := by
        simp only [abs_mul]
        gcongr
      _ = H + E + (1 + 3 * H + H ^ 2) * B := by ring
      _ ≤ _ := by
        gcongr
        nlinarith [sq_nonneg H]
  intro i
  fin_cases i
  · exact h0
  · exact h1.trans (hbig.trans (by linarith))
  · exact h2.trans (hbig.trans (by linarith))
  · have hBB : B ≤ (1 + H) * B := by nlinarith
    exact hL3.trans (hBB.trans (hbig.trans (by linarith)))

end Submission.Obl.k4_wide_three_layer_scalar_inputs
