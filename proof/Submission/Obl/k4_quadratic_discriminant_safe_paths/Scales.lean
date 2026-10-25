import Mathlib

namespace Submission.Obl.k4_quadratic_discriminant_safe_paths

/-- Fixed positive constants can be absorbed into one absolute radius power,
uniformly down to the endpoint `A = 2`. -/
theorem exists_power_radius (L K J : ℝ) (hL : 0 ≤ L) (hK : 0 < K)
    (hJ : 0 < J) (n : ℕ) : ∃ C : ℕ, 0 < C ∧ ∀ A : ℝ, 2 ≤ A →
      A ^ (-(C : ℝ)) ≤ 1 / 2 ∧
      (1 + L * A) * A ^ (-(C : ℝ)) ≤
        (K * (A ^ n)⁻¹) * (J / A) ^ 2 := by
  let θ : ℝ := min (1 / 2) (K * J ^ 2 / (1 + L))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθhalf : θ ≤ 1 / 2 := min_le_left _ _
  have hθscale : θ * (1 + L) ≤ K * J ^ 2 := by
    exact (le_div_iff₀ (by linarith : 0 < 1 + L)).mp (min_le_right _ _)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt θ⁻¹ (by norm_num : (1 : ℝ) < 2)
  let C := m + n + 3
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro A hA
  have hApos : 0 < A := by linarith
  have hAone : 1 ≤ A := by linarith
  have hpow : θ⁻¹ < A ^ m :=
    hm.trans_le (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hA m)
  have hsmall : (A ^ m)⁻¹ ≤ θ := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hθ) hpow.le
  have hrEq : A ^ (-(C : ℝ)) = (A ^ C)⁻¹ := by
    rw [Real.rpow_neg hApos.le, Real.rpow_natCast]
  have hrSplit : (A ^ C)⁻¹ = (A ^ m)⁻¹ * (A ^ (n + 3))⁻¹ := by
    dsimp [C]
    rw [show m + n + 3 = m + (n + 3) by omega, pow_add, mul_inv]
  have htail : (A ^ (n + 3))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hAone)
  have hrhalf : A ^ (-(C : ℝ)) ≤ 1 / 2 := by
    rw [hrEq, hrSplit]
    calc
      _ ≤ θ * 1 := mul_le_mul hsmall htail (by positivity) hθ.le
      _ ≤ 1 / 2 := by simpa using hθhalf
  refine ⟨hrhalf, ?_⟩
  have hcoeff : 1 + L * A ≤ (1 + L) * A := by nlinarith
  have hconstant : (1 + L) * (A ^ m)⁻¹ ≤ K * J ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hsmall (by linarith : 0 ≤ 1 + L)
    nlinarith
  rw [hrEq, hrSplit]
  calc
    _ ≤ ((1 + L) * A) * ((A ^ m)⁻¹ * (A ^ (n + 3))⁻¹) := by gcongr
    _ = ((1 + L) * (A ^ m)⁻¹) * (A ^ (n + 2))⁻¹ := by
      rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
      field_simp
    _ ≤ (K * J ^ 2) * (A ^ (n + 2))⁻¹ := by gcongr
    _ = (K * (A ^ n)⁻¹) * (J / A) ^ 2 := by
      rw [pow_add]
      field_simp

/-- Choose the detour strip width relative to the original complex disk. -/
theorem exists_detour_scale : ∃ J : ℝ, 0 < J ∧ J ≤ 1 / 2 ∧
    ∀ A : ℝ, 2 ≤ A → 0 < J / A ∧ J / A ≤ 1 / 2 ∧
      ENNReal.ofReal (64 * (J / A)) ≤ ENNReal.ofReal (A⁻¹ / 2) *
        MeasureTheory.volume (Metric.closedBall (1 / 2 : ℂ) (1 / 4)) := by
  let V := MeasureTheory.volume (Metric.closedBall (1 / 2 : ℂ) (1 / 4))
  have hVpos : 0 < V := Metric.measure_closedBall_pos _ _ (by norm_num)
  have hVfin : V ≠ ⊤ := (isCompact_closedBall _ _).measure_ne_top
  let v := V.toReal
  have hv : 0 < v := ENNReal.toReal_pos hVpos.ne' hVfin
  let J := min (v / 128) (1 / 2)
  have hJ : 0 < J := by dsimp [J]; positivity
  have hJhalf : J ≤ 1 / 2 := min_le_right _ _
  have hJv : J ≤ v / 128 := min_le_left _ _
  refine ⟨J, hJ, hJhalf, ?_⟩
  intro A hA
  have hApos : 0 < A := by linarith
  refine ⟨div_pos hJ hApos, ?_, ?_⟩
  · apply (div_le_iff₀ hApos).mpr
    linarith
  · have hnum : 64 * (J / A) ≤ (A⁻¹ / 2) * v := by
      calc
        _ = (64 * J) / A := by ring
        _ ≤ (v / 2) / A := by gcongr; linarith
        _ = (A⁻¹ / 2) * v := by ring
    have hVeq : ENNReal.ofReal v = V := ENNReal.ofReal_toReal hVfin
    change ENNReal.ofReal (64 * (J / A)) ≤ ENNReal.ofReal (A⁻¹ / 2) * V
    rw [← hVeq, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hnum

end Submission.Obl.k4_quadratic_discriminant_safe_paths
