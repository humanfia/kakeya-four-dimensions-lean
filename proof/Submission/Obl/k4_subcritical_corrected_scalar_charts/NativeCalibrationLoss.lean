/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeCalibrationLoss.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeChildCalibration

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

noncomputable section

def nativeOriginalLoss (C K : ℝ) : ℝ :=
  nativeCalibrationLoss C (K ^ 2) (1 / K ^ 3) (27 * (4 * K + 6) * K)

/-- The common hidden-width and native-volume factor cancels exactly. -/
theorem original_native_loss_cancellation (C K q a d : ℝ) (hq : 0 < q) (ha : 0 < a) :
    nativeCalibrationLoss C (K ^ 2) (q ^ 4 * a ^ d / K ^ 3)
      (27 * ((4 * K + 6) * (K * a ^ d)) * q ^ 4) = nativeOriginalLoss C K := by
  have hs : q ^ 4 * a ^ d ≠ 0 := (by positivity : 0 < q ^ 4 * a ^ d).ne'
  have hm : q ^ 4 * a ^ d / K ^ 3 = (q ^ 4 * a ^ d) * (1 / K ^ 3) := by ring
  have hβ : 27 * ((4 * K + 6) * (K * a ^ d)) * q ^ 4 =
      (q ^ 4 * a ^ d) * (27 * (4 * K + 6) * K) := by ring
  rw [hm, hβ, nativeCalibrationLoss_common_factor C (K ^ 2) _ _ _ hs]
  rfl

/-- The remaining loss is a fixed polynomial in the original slack. -/
theorem nativeOriginalLoss_formula {C K : ℝ} (hK : 1 ≤ K) :
    nativeOriginalLoss C K = 128 * C * (884736 * (4 * K + 6) * K ^ 10) ^ 3 := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  unfold nativeOriginalLoss nativeCalibrationLoss
  congr 2
  field_simp
  ring

theorem nativeOriginalLoss_bound {C K : ℝ} (hC : 0 ≤ C) (hK : 1 ≤ K) :
    nativeOriginalLoss C K ≤ (128 * (8847360 : ℝ) ^ 3) * C * K ^ 33 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  rw [nativeOriginalLoss_formula hK]
  have hb : 884736 * (4 * K + 6) * K ^ 10 ≤ 8847360 * K ^ 11 := by
    have hlin : 4 * K + 6 ≤ 10 * K := by linarith
    calc
      _ ≤ 884736 * (10 * K) * K ^ 10 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 128 * C * (8847360 * K ^ 11) ^ 3 := by gcongr
    _ = _ := by ring

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
