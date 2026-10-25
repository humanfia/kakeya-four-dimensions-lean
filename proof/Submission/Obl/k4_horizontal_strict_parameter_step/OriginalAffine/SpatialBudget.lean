/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/SpatialBudget.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.CountNumerics

namespace Submission.Obl.k4_horizontal_strict_parameter_step

/-- The deterministic child gradient budget also applies to a pointwise
prepared loss, once its explicit power inequality has been checked. -/
theorem child_spatial_budget_of_floor {N K κ u s₀ E q w : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hroom : -u * s₀ + 2 * κ * (s₀ + E) ≤ -8 * E)
    (hsmall : 14155776 * K ^ 12 * N ^ (-8 * E) ≤ N ^ (-E))
    (hq : 0 < q) (hw : N ^ (-E) ≤ w)
    (hqmin : N ^ (-κ * (s₀ + E)) / K ≤ q) :
    14155776 * K ^ 10 * N ^ (-u * s₀) ≤ w * q ^ 2 := by
  have hNp : 0 < N := zero_lt_one.trans_le (hN)
  have hKp : 0 < K := zero_lt_one.trans_le (hK)
  let G := N ^ (-κ * (s₀ + E))
  have hGp : 0 < G := Real.rpow_pos_of_pos hNp _
  have hGq : G ≤ K * q := by
    simpa only [G, mul_comm] using (div_le_iff₀ hKp).mp hqmin
  have hGq2 : G ^ 2 ≤ K ^ 2 * q ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hGp.le hGq 2
  have hid : G ^ 2 * N ^ (-8 * E) = N ^ (-2 * κ * (s₀ + E) - 8 * E) := by
    dsimp [G]
    rw [pow_two, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
    congr 1
    ring
  have hD : N ^ (-u * s₀) ≤ G ^ 2 * N ^ (-8 * E) := by
    rw [hid]
    exact Real.rpow_le_rpow_of_exponent_le (hN) (by linarith only [hroom])
  have hDs : N ^ (-u * s₀) ≤ K ^ 2 * q ^ 2 * N ^ (-8 * E) :=
    hD.trans (mul_le_mul_of_nonneg_right hGq2 (Real.rpow_nonneg hNp.le _))
  calc
    _ ≤ 14155776 * K ^ 10 * (K ^ 2 * q ^ 2 * N ^ (-8 * E)) :=
      mul_le_mul_of_nonneg_left hDs (by positivity)
    _ = (14155776 * K ^ 12 * N ^ (-8 * E)) * q ^ 2 := by ring
    _ ≤ N ^ (-E) * q ^ 2 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hw (sq_nonneg _)

end Submission.Obl.k4_horizontal_strict_parameter_step
