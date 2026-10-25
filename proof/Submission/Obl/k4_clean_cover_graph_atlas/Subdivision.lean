import Submission.Obl.k4_clean_cover_graph_atlas.Frames

namespace Submission.Obl.k4_clean_cover_graph_atlas

/-- A common dyadic subdivision just below any nonnegative real-power budget.
Its side length is within a factor two of the inverse budget. -/
theorem exists_budget_subdivision {N a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) :
    ∃ s₀ : ℕ, (2 : ℝ) ^ s₀ ≤ N ^ a ∧ N ^ a < 2 * (2 : ℝ) ^ s₀ ∧
      side s₀ ≤ 2 * N ^ (-a) ∧
      ∀ T : ℕ, (2 : ℝ) ^ (T + s₀) ≤ (2 : ℝ) ^ T * N ^ a := by
  have hN0 : 0 < N := by linarith
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_nat_pow_near (Real.one_le_rpow hN ha)
    (by norm_num : (1 : ℝ) < 2)
  rw [pow_succ] at hs₀'
  have hlarge : N ^ a < 2 * (2 : ℝ) ^ s₀ := by linarith
  refine ⟨s₀, hs₀, hlarge, ?_, fun T => ?_⟩
  · rw [side, Real.rpow_neg hN0.le]
    have hpow : 0 < N ^ a := Real.rpow_pos_of_pos hN0 a
    have htwo : 0 < (2 : ℝ) ^ s₀ := by positivity
    have hh : (1 : ℝ) / (2 : ℝ) ^ s₀ ≤ 2 / N ^ a :=
      (div_le_div_iff₀ htwo hpow).mpr (by simpa only [one_mul] using hlarge.le)
    simpa only [one_div, div_eq_mul_inv, one_mul] using hh
  · rw [pow_add]
    exact mul_le_mul_of_nonneg_left hs₀ (by positivity)

/-- The bounded integer midpoint-box range has one fixed polynomial exponent. -/
theorem ceil_box_range_bound {N κ : ℝ} {k m : ℕ}
    (hN : 2 ≤ N) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ k)
    {s₀ : ℕ} (hs₀ : (2 : ℝ) ^ s₀ ≤ N ^ m) :
    (⌈κ * (2 : ℝ) ^ s₀⌉₊ : ℝ) ≤ N ^ (k + m + 1) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hprod : κ * (2 : ℝ) ^ s₀ ≤ N ^ (k + m) := by
    rw [pow_add]
    exact mul_le_mul hκ hs₀ (by positivity) (by positivity)
  have hceil : (⌈κ * (2 : ℝ) ^ s₀⌉₊ : ℝ) < κ * (2 : ℝ) ^ s₀ + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hunit : 1 ≤ N ^ (k + m) := one_le_pow₀ hN1
  calc
    _ ≤ 2 * N ^ (k + m) := by linarith
    _ ≤ N ^ (k + m + 1) := by
      rw [pow_succ]
      have hh := mul_le_mul_of_nonneg_right hN (pow_nonneg hN0.le (k + m))
      nlinarith

/-- The common subdivision is short enough to preserve candidate derivative signs
once its fixed exponent dominates four times the input fit exponent. -/
theorem subdivision_sign_budget {N a u : ℝ} {s₀ : ℕ}
    (hN : 1 ≤ N) (hside : side s₀ ≤ 2 * N ^ (-a))
    (hsmall : 4 * u ≤ a) (hlarge : 8 ≤ N ^ (a / 2)) :
    4 * (N ^ u) ^ 2 * side s₀ ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have hp : (N ^ u) ^ 2 = N ^ (2 * u) := by
    rw [show 2 * u = u * 2 by ring, Real.rpow_mul hN0.le]
    norm_num
  calc
    _ ≤ 4 * (N ^ u) ^ 2 * (2 * N ^ (-a)) :=
      mul_le_mul_of_nonneg_left hside (by positivity)
    _ = 8 * N ^ (2 * u - a) := by
      rw [hp, show 4 * N ^ (2 * u) * (2 * N ^ (-a)) =
        8 * (N ^ (2 * u) * N ^ (-a)) by ring, ← Real.rpow_add hN0]
      simp only [sub_eq_add_neg]
    _ ≤ 8 * N ^ (-(a / 2)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by norm_num)
    _ ≤ N ^ (a / 2) * N ^ (-(a / 2)) :=
      mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = 1 := by rw [← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero]

end Submission.Obl.k4_clean_cover_graph_atlas
