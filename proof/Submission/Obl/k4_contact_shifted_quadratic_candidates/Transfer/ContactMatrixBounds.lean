/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/ContactMatrixBounds.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.ContactMatrix
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameSourceNumerics

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open Matrix

noncomputable section

/-- A contact matrix has a quadratic, rather than quartic, inverse-width
cost in each row. Its determinant is handled separately. -/
theorem contactFrameMatrix_row_bound {t q Z K : ℝ} (hq : 0 < q) (hq₁ : q ≤ 1)
    (hK : 1 ≤ K) (ht : |t| ≤ 1) (hZ : |Z| ≤ 2 * K) (i : Fin 3) :
    (∑ j, |contactFrameMatrix t q Z i j|) ≤ (2 * K + 2) * (q⁻¹) ^ 2 := by
  have hi : 1 ≤ q⁻¹ := (one_le_inv₀ hq).mpr hq₁
  have hi₀ : 0 ≤ q⁻¹ := le_of_lt (inv_pos.mpr hq)
  have hs : q⁻¹ ≤ (q⁻¹) ^ 2 := by nlinarith
  have hZ' := mul_le_mul_of_nonneg_right hZ (sq_nonneg q⁻¹)
  have ht' := mul_le_mul_of_nonneg_right ht (sq_nonneg q⁻¹)
  fin_cases i <;>
    simp [Fin.sum_univ_three, contactFrameMatrix, abs_of_pos hq,
      div_eq_mul_inv, ← inv_pow] <;> nlinarith [sq_nonneg q⁻¹]

/-- All row costs of a bounded parent chart fit one fixed power. This
power only chooses a fine original mesh and is not charged to the cap. -/
theorem contactFrameMatrix_row_power_bound {N K q t Z s κ : ℝ}
    (hN : 2 ≤ N) (hK : 1 ≤ K) (hKN : K ≤ N) (hs : 0 ≤ s) (hκ : κ ≤ 1)
    (hq : 0 < q) (hq₁ : q ≤ 1) (ht : |t| ≤ 1) (hZ : |Z| ≤ 2 * K)
    (hcount : q⁻¹ ≤ K * N ^ (κ * s)) (i : Fin 3) :
    (∑ j, |contactFrameMatrix t q Z i j|) ≤ N ^ (2 * s + 5) := by
  have hN₀ : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hq' : q⁻¹ ≤ N ^ (s + 1) := by
    calc
      q⁻¹ ≤ K * N ^ (κ * s) := hcount
      _ ≤ N * N ^ s := mul_le_mul hKN
        (Real.rpow_le_rpow_of_exponent_le hN₁ (by nlinarith [mul_le_mul_of_nonneg_right hκ hs]))
        (Real.rpow_nonneg hN₀.le _) hN₀.le
      _ = N ^ (s + 1) := by rw [Real.rpow_add hN₀, Real.rpow_one, mul_comm]
  have hnum : 2 * K + 2 ≤ N ^ (3 : ℕ) := by
    have : N * (N - 2) ^ 2 ≥ 0 := mul_nonneg hN₀.le (sq_nonneg (N - 2))
    nlinarith
  calc
    _ ≤ (2 * K + 2) * (q⁻¹) ^ 2 := contactFrameMatrix_row_bound hq hq₁ hK ht hZ i
    _ ≤ N ^ (3 : ℕ) * (N ^ (s + 1)) ^ (2 : ℕ) :=
      mul_le_mul hnum (pow_le_pow_left₀ (inv_nonneg.mpr hq.le) hq' 2)
        (sq_nonneg _) (pow_nonneg hN₀.le _)
    _ = N ^ (2 * s + 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN₀.le,
        ← Real.rpow_add hN₀]
      congr 1
      ring

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
