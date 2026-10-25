import Submission.Obl.k4_matching_abstract_switching_mixture.Parameters
import Submission.Obl.k4_matching_abstract_switching_mixture.Endpoint

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open MeasureTheory

lemma upgrade_pullback_bound {m : ℕ} {N B K θ : ℝ}
    (hN : 0 < N) (hB : 1 ≤ B) (hK : 2 ≤ K)
    (U : Fin (m + 1) → ℝ) (s₀ : ℝ) (T : Set (ℝ × (Fin m → ℝ)))
    (h : 1 / 2 ≤ (Real.exp (θ * Real.log N) * (B / smallError m) * (2 * K)) ^ (m + 1) *
      (volume (pullback (sizeBound m B K) U s₀ T)).toReal) :
    1 / 4 ≤ sizeBound m B K * N ^ (((m : ℝ) + 1) * θ) *
      (volume (pullback (sizeBound m B K) U s₀ T)).toReal := by
  have hpow : (N ^ θ) ^ (m + 1) = N ^ (((m : ℝ) + 1) * θ) := by
    rw [← Real.rpow_mul_natCast hN.le]
    congr 1
    push_cast
    ring
  have hexp : Real.exp (θ * Real.log N) = N ^ θ := by
    rw [Real.rpow_def_of_pos hN]
    congr 1
    ring
  have hcoef : (Real.exp (θ * Real.log N) * (B / smallError m) * (2 * K)) ^ (m + 1)
      ≤ sizeBound m B K * N ^ (((m : ℝ) + 1) * θ) := by
    calc
      (Real.exp (θ * Real.log N) * (B / smallError m) * (2 * K)) ^ (m + 1) =
          (2 * B * K / smallError m) ^ (m + 1) * (N ^ θ) ^ (m + 1) := by
            rw [hexp, ← mul_pow]
            congr 1
            ring
      _ = (2 * B * K / smallError m) ^ (m + 1) * N ^ (((m : ℝ) + 1) * θ) := by rw [hpow]
      _ ≤ sizeBound m B K * N ^ (((m : ℝ) + 1) * θ) :=
        mul_le_mul_of_nonneg_right (sizeBound_bounds m hB hK).2.2.2 (by positivity)
  have hlarge := h.trans (mul_le_mul_of_nonneg_right hcoef ENNReal.toReal_nonneg)
  linarith

end Submission.Obl.k4_matching_abstract_switching_mixture
