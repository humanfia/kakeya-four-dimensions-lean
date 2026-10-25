/- Numerical bounds generalized from this LOT tree, obligation o200,
   session x0829, commit a965423f,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ModelNativeCalibration.lean.
   Here the source reference mass m need not be K inverse. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

theorem native_mesh_ratio_bound {K m : ℝ} (hK : 1 ≤ K) (hm : 0 < m) :
    0 ≤ 96 / (m / (((2 * K + 5) * K) * (8 * K) ^ 3)) ∧
      96 / (m / (((2 * K + 5) * K) * (8 * K) ^ 3)) ≤ 344064 * K ^ 5 / m := by
  have hK₀ : 0 < K := by linarith
  constructor
  · positivity
  · have he : 96 / (m / (((2 * K + 5) * K) * (8 * K) ^ 3)) =
        49152 * (2 * K + 5) * K ^ 4 / m := by field_simp; ring
    rw [he]
    apply (div_le_div_iff_of_pos_right hm).mpr
    calc
      _ ≤ 49152 * (7 * K) * K ^ 4 := by gcongr; linarith
      _ = _ := by ring

theorem native_mesh_coefficient_budget {K m C : ℝ} (hK : 1 ≤ K)
    (hm : 0 < m) (hC : 0 ≤ C) :
    54 * C * (96 / (m / (((2 * K + 5) * K) * (8 * K) ^ 3))) ^ 6 * (3 * K) ≤
      (162 * C * 344064 ^ 6) * K ^ 31 / m ^ 6 := by
  have hK₀ : 0 < K := by linarith
  calc
    _ ≤ 54 * C * (344064 * K ^ 5 / m) ^ 6 * (3 * K) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ 3 * K)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 54 * C)
      exact pow_le_pow_left₀ (native_mesh_ratio_bound hK hm).1
        (native_mesh_ratio_bound hK hm).2 6
    _ = _ := by ring

theorem native_mesh_absorption_budget {K m C Lip h : ℝ}
    (hK : 1 ≤ K) (hm : 0 < m) (hC : 0 ≤ C) (hLip : 0 ≤ Lip) (hh : 0 ≤ h) :
    54 * Lip * C * (96 / (m / (((2 * K + 5) * K) * (8 * K) ^ 3))) ^ 6 *
        (h / (8 * K)) ≤ (54 * Lip * C * 344064 ^ 6) * K ^ 30 * h / m ^ 6 := by
  have hK₀ : 0 < K := by linarith
  calc
    _ ≤ 54 * Lip * C * (344064 * K ^ 5 / m) ^ 6 * (h / (8 * K)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ h / (8 * K))
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 54 * Lip * C)
      exact pow_le_pow_left₀ (native_mesh_ratio_bound hK hm).1
        (native_mesh_ratio_bound hK hm).2 6
    _ ≤ 54 * Lip * C * (344064 * K ^ 5 / m) ^ 6 * h :=
      mul_le_mul_of_nonneg_left (div_le_self hh (by linarith : 1 ≤ 8 * K)) (by positivity)
    _ = _ := by ring

theorem fixed_mass_calibration_identity {N : ℝ} (hN : 0 < N) (B r A : ℝ) :
    A * N ^ (-r) / (N ^ (-B)) ^ (6 : ℕ) = A * N ^ (6 * B - r) := by
  calc
    _ = A * (N ^ (-r) / (N ^ (-B)) ^ (6 : ℕ)) := by ring
    _ = A * N ^ (-r - (-B * 6)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_sub hN]
      norm_num
    _ = _ := by congr 1; ring

theorem fine_native_absorption {N K Lip B r s : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hLip : 0 ≤ Lip) (hLipN : 2 * Lip ≤ N)
    (hrs : s + (6 * B + 2) ≤ r) :
    2 * Lip * N ^ (6 * B + 1) * (N ^ (-r) / (8 * K)) ≤ K * N ^ (-s) := by
  have hN₀ : 0 < N := by linarith
  have hδ : 0 ≤ N ^ (-r) := Real.rpow_nonneg hN₀.le _
  calc
    _ ≤ 2 * Lip * N ^ (6 * B + 1) * N ^ (-r) :=
      mul_le_mul_of_nonneg_left (div_le_self hδ (by linarith : 1 ≤ 8 * K)) (by positivity)
    _ ≤ N * N ^ (6 * B + 1) * N ^ (-r) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLipN (Real.rpow_nonneg hN₀.le _)) hδ
    _ = N ^ (6 * B + 2 - r) := by
      calc
        _ = N ^ (1 : ℝ) * N ^ (6 * B + 1) * N ^ (-r) := by rw [Real.rpow_one]
        _ = N ^ (1 + (6 * B + 1) + (-r)) := by
          rw [← Real.rpow_add hN₀, ← Real.rpow_add hN₀]
        _ = _ := by congr 1; ring
    _ ≤ N ^ (-s) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ ≤ K * N ^ (-s) := le_mul_of_one_le_left (Real.rpow_nonneg hN₀.le _) hK

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
