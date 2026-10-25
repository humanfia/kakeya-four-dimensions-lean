import Submission.Obl.k4_stable_native_signal_oscillation.GoodSet

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial MeasureTheory Set

lemma witness_volume (μ : Measure NativePoint) [IsProbabilityMeasure μ] {K : ℝ}
    (hK : 0 < K) (hd : Measure.map nativeBase μ ≤ ENNReal.ofReal K • volume)
    (T : Set BasePoint) (hT : MeasurableSet T) (hfull : ∀ᵐ p ∂μ, nativeBase p ∈ T) :
    ENNReal.ofReal K⁻¹ ≤ volume T := by
  have hprob : (Measure.map nativeBase μ) T = 1 := by
    rw [Measure.map_apply measurable_nativeBase hT]
    exact (mem_ae_iff_prob_eq_one (hT.preimage measurable_nativeBase)).mp hfull
  rw [ENNReal.ofReal_inv_of_pos hK]
  apply (ENNReal.inv_le_iff_le_mul
    (fun _ => (ENNReal.ofReal_pos.mpr hK).ne') (fun h => (ENNReal.ofReal_ne_top h).elim)).mpr
  calc
    1 = (Measure.map nativeBase μ) T := hprob.symm
    _ ≤ (ENNReal.ofReal K • volume) T := hd T
    _ = ENNReal.ofReal K * volume T := Measure.smul_apply _ _ _

end Submission.Obl.k4_stable_native_signal_oscillation
