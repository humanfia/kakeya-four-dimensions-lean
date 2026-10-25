import Mathlib
import Submission.Obl.k4_oss_unit_decay.Numerics

namespace Submission.Obl.k4_oss_level_finite_gain

/-- A finite cardinality below a power has an exact dimension at that scale. -/
theorem exists_card_dimension {δ N D : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hN : 1 ≤ N) (hcap : N ≤ δ ^ (-D)) :
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ D ∧ δ ^ (-d) = N := by
  let d := Real.log N / (-Real.log δ)
  have hlog : 0 < -Real.log δ := neg_pos.mpr (Real.log_neg hδ hδ1)
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hd0 : 0 ≤ d := div_nonneg (Real.log_nonneg hN) hlog.le
  have hdD : d ≤ D := by
    apply (div_le_iff₀ hlog).mpr
    have hh := Real.log_le_log hNpos hcap
    rw [Real.log_rpow hδ] at hh
    nlinarith only [hh]
  have heq : Real.log δ * (-d) = Real.log N := by
    have hh := div_mul_cancel₀ (Real.log N) (ne_of_gt hlog)
    change d * (-Real.log δ) = Real.log N at hh
    nlinarith only [hh]
  refine ⟨d, hd0, hdD, ?_⟩
  rw [Real.rpow_def_of_pos hδ, heq, Real.exp_log hNpos]

/-- Comparable cardinalities lie in the same dimension window. -/
theorem size_window {δ θ d η N M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hηθ : η ≤ θ) (hN : 0 ≤ N) (hbase : δ ^ (-d) = N)
    (hNM : N ≤ δ ^ (-η) * M) (hMN : M ≤ δ ^ (-η) * N) :
    δ ^ (θ - d) ≤ M ∧ M ≤ δ ^ (-d - θ) := by
  constructor
  · apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hδ (-η))).mp
    calc
      δ ^ (-η) * δ ^ (θ - d) = δ ^ (θ - η) * N := by
        rw [← hbase, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ 1 * N := mul_le_mul_of_nonneg_right
        (Real.rpow_le_one hδ.le hδ1 (sub_nonneg.mpr hηθ)) hN
      _ = N := one_mul _
      _ ≤ δ ^ (-η) * M := hNM
  · calc
      M ≤ δ ^ (-η) * N := hMN
      _ ≤ δ ^ (-θ) * N := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηθ)) hN
      _ = δ ^ (-d - θ) := by
        rw [← hbase, ← Real.rpow_add hδ]
        congr 1
        ring

/-- The scalar mass bounds remove the level weights from the finite gain. -/
theorem weighted_gain_bound {δ θ a Z q₁ q₂ N M : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (haθ : 2 * a ≤ θ)
    (hZ : 0 ≤ Z) (hq₁ : 0 ≤ q₁) (hN : 0 ≤ N)
    (hmass : q₁ * N ≤ 1) (hsquare : q₂ ^ 2 * M ≤ Z) :
    (q₁ ^ 2 * q₂ ^ 2) * (δ ^ θ * N ^ 2 * M) ≤ δ ^ (2 * a) * Z := by
  have hmass2 : (q₁ * N) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (mul_nonneg hq₁ hN) hmass 2
  calc
    _ = (δ ^ θ * (q₁ * N) ^ 2) * (q₂ ^ 2 * M) := by ring
    _ ≤ (δ ^ θ * (q₁ * N) ^ 2) * Z :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ ≤ (δ ^ θ * 1) * Z := by gcongr
    _ ≤ δ ^ (2 * a) * Z := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 haθ) hZ

end Submission.Obl.k4_oss_level_finite_gain
