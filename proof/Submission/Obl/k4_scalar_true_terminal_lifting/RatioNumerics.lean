import Mathlib

open scoped ENNReal

namespace Submission.Obl.k4_scalar_true_terminal_lifting

/-- A ratio-bad assignment makes its raw selected density small whenever the
original terminal density is above its lower threshold and the normalized
terminal density is below its upper threshold. -/
theorem ratio_bad_implies_low_density
    {N J : ℝ} (hN : 0 < N) (hJ : 0 < J) (fp fq δ τ : ℝ)
    (a old new : ℝ≥0∞)
    (hbad : a < ENNReal.ofReal (N ^ (fq - fp - δ) * J))
    (hold : ENNReal.ofReal (N ^ (-fp - τ)) ≤ old)
    (hnew : new ≤ ENNReal.ofReal (N ^ (-fq + τ))) :
    (a / ENNReal.ofReal J) * new < ENNReal.ofReal (N ^ (-δ + 2 * τ)) * old := by
  have hfac : 0 < N ^ (fq - fp - δ) := Real.rpow_pos_of_pos hN _
  have hu : 0 < N ^ (-fq + τ) := Real.rpow_pos_of_pos hN _
  have hη : 0 < N ^ (-δ + 2 * τ) := Real.rpow_pos_of_pos hN _
  rw [ENNReal.ofReal_mul hfac.le] at hbad
  have hr : a / ENNReal.ofReal J < ENNReal.ofReal (N ^ (fq - fp - δ)) :=
    (ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hJ))
      (Or.inl ENNReal.ofReal_ne_top)).mpr hbad
  have hpow : N ^ (fq - fp - δ) * N ^ (-fq + τ) =
      N ^ (-δ + 2 * τ) * N ^ (-fp - τ) := by
    rw [← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  calc
    _ ≤ (a / ENNReal.ofReal J) * ENNReal.ofReal (N ^ (-fq + τ)) :=
      mul_le_mul' le_rfl hnew
    _ < ENNReal.ofReal (N ^ (fq - fp - δ)) * ENNReal.ofReal (N ^ (-fq + τ)) :=
      ENNReal.mul_lt_mul_left (ENNReal.ofReal_ne_zero_iff.mpr hu) ENNReal.ofReal_ne_top hr
    _ = ENNReal.ofReal (N ^ (-δ + 2 * τ)) * ENNReal.ofReal (N ^ (-fp - τ)) := by
      rw [← ENNReal.ofReal_mul hfac.le, hpow, ENNReal.ofReal_mul hη.le]
    _ ≤ _ := mul_le_mul' le_rfl hold

/-- On a ratio-good parent world the child's true floor lifts to the original
terminal floor. The ratio threshold loses only the prescribed exponent `δ`. -/
theorem terminal_floor_lifting
    {N Ji Jd dt D : ℝ} (hN : 0 < N) (hJi : 0 < Ji) (hJd : 0 < Jd)
    (hdt : 0 < dt) (hD : 0 < D) (fp fq δ ε : ℝ)
    (a mass : ℝ≥0∞)
    (hratio : ENNReal.ofReal (N ^ (fq - fp - δ) * Ji) ≤ a)
    (hfloor : ENNReal.ofReal (N ^ (-fq) * Jd / (N ^ ε * D)) ≤ mass) :
    ENNReal.ofReal (N ^ (-fp) * (Ji * Jd) * dt / (N ^ (δ + ε) * D)) ≤
      ENNReal.ofReal dt * a * mass := by
  have hfac : 0 ≤ N ^ (fq - fp - δ) * Ji := by positivity
  have hchild : 0 ≤ N ^ (-fq) * Jd / (N ^ ε * D) := by positivity
  have hpow : N ^ (-fp) / N ^ (δ + ε) =
      N ^ (fq - fp - δ) * N ^ (-fq) / N ^ ε := by
    rw [← Real.rpow_add hN, ← Real.rpow_sub hN, ← Real.rpow_sub hN]
    congr 1
    ring
  have heq : N ^ (-fp) * (Ji * Jd) * dt / (N ^ (δ + ε) * D) =
      dt * (N ^ (fq - fp - δ) * Ji) * (N ^ (-fq) * Jd / (N ^ ε * D)) := by
    calc
      _ = (N ^ (-fp) / N ^ (δ + ε)) * (Ji * Jd * dt / D) := by ring
      _ = _ := by rw [hpow]; ring
  calc
    _ = ENNReal.ofReal dt * ENNReal.ofReal (N ^ (fq - fp - δ) * Ji) *
        ENNReal.ofReal (N ^ (-fq) * Jd / (N ^ ε * D)) := by
      rw [heq, ENNReal.ofReal_mul (mul_nonneg hdt.le hfac), ENNReal.ofReal_mul hdt.le]
    _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hratio) hfloor

end Submission.Obl.k4_scalar_true_terminal_lifting
