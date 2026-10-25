import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_horizontal_three_traversal_spreading

open Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- The fine geometric error and all polynomial switching losses fit into
an arbitrarily small prescribed output power. -/
theorem choose_scales (C S a ε : ℝ) (hS : 0 < S) (ha : 0 < a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N →
        2 ≤ N ^ κ ∧ 1 ≤ N ^ δ ∧ N ^ δ + N ^ (-20 * a) ≤ N ^ κ ∧
        N ^ (-20 * a) ≤ (N ^ κ)⁻¹ ∧
        600 * (N ^ κ) ^ 3 * N ^ (-20 * a) ≤ N ^ (-a) / 2 ∧
        N ^ δ * (N ^ δ * (2 / N ^ κ) ^ S) + 144 * N ^ δ / N ^ κ ≤ 1 / 9 ∧
        C * (N ^ κ) ^ 24 * (N ^ δ) ^ 6 ≤ N ^ ε := by
  let κ : ℝ := min a ε / 100
  have hκ : 0 < κ := div_pos (lt_min ha hε) (by norm_num)
  have hκa : 100 * κ ≤ a := by dsimp [κ]; nlinarith [min_le_left a ε]
  have hκε : 100 * κ ≤ ε := by dsimp [κ]; nlinarith [min_le_right a ε]
  let δ : ℝ := min κ (κ * S) / 100
  have hδ : 0 < δ := div_pos (lt_min hκ (mul_pos hκ hS)) (by norm_num)
  have hδκ : 100 * δ ≤ κ := by dsimp [δ]; nlinarith [min_le_left κ (κ * S)]
  have hδS : 100 * δ ≤ κ * S := by dsimp [δ]; nlinarith [min_le_right κ (κ * S)]
  have hδε : δ ≤ ε := by linarith
  have hδlt : δ < κ := by linarith
  have hpall : 2 * δ - κ * S < 0 := by linarith
  have hgeom : 3 * κ - 20 * a < -a := by linarith
  have hcost : 24 * κ + 6 * δ < ε := by linarith
  have hev : ∀ᶠ N : ℝ in atTop,
      2 ≤ N ^ κ ∧ 1 ≤ N ^ δ ∧ N ^ δ + N ^ (-20 * a) ≤ N ^ κ ∧
      N ^ (-20 * a) ≤ (N ^ κ)⁻¹ ∧
      600 * (N ^ κ) ^ 3 * N ^ (-20 * a) ≤ N ^ (-a) / 2 ∧
      N ^ δ * (N ^ δ * (2 / N ^ κ) ^ S) + 144 * N ^ δ / N ^ κ ≤ 1 / 9 ∧
      C * (N ^ κ) ^ 24 * (N ^ δ) ^ 6 ≤ N ^ ε := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      eventually_const_mul_rpow_le 2 hκ,
      eventually_const_mul_rpow_le 2 hδlt,
      eventually_const_mul_rpow_le 2 (show -20 * a < κ by linarith),
      eventually_const_mul_rpow_le 1200 hgeom,
      eventually_const_mul_rpow_le (36 * (2 : ℝ) ^ S) hpall,
      eventually_const_mul_rpow_le 5184 (show δ - κ < 0 by linarith),
      eventually_const_mul_rpow_le C hcost] with N hN hK hB hh hg hp ht hc
    have hN0 : 0 < N := by linarith
    have hN1 : 1 ≤ N := by linarith
    have hK0 : 0 < N ^ κ := Real.rpow_pos_of_pos hN0 _
    simp only [Real.rpow_zero, mul_one] at hK hp ht
    have hgeom_eq : (N ^ κ) ^ 3 * N ^ (-20 * a) = N ^ (3 * κ - 20 * a) := by
      rw [← Real.rpow_mul_natCast hN0.le, ← Real.rpow_add hN0]
      congr 1
      ring
    have hpal_eq : N ^ δ * (N ^ δ * (2 / N ^ κ) ^ S) =
        (2 : ℝ) ^ S * N ^ (2 * δ - κ * S) := by
      rw [Real.div_rpow (by norm_num) hK0.le, ← Real.rpow_mul hN0.le,
        Real.rpow_sub hN0, show 2 * δ = δ + δ by ring, Real.rpow_add hN0]
      ring
    have htime_eq : 144 * N ^ δ / N ^ κ = 144 * N ^ (δ - κ) := by
      rw [Real.rpow_sub hN0]
      ring
    have hcost_eq : C * (N ^ κ) ^ 24 * (N ^ δ) ^ 6 = C * N ^ (24 * κ + 6 * δ) := by
      rw [← Real.rpow_mul_natCast hN0.le, ← Real.rpow_mul_natCast hN0.le,
        mul_assoc, ← Real.rpow_add hN0]
      congr 1
      ring
    refine ⟨hK, Real.one_le_rpow hN1 hδ.le, by linarith, ?_, ?_, ?_, ?_⟩
    · have h := Real.rpow_le_rpow_of_exponent_le hN1 (show -20 * a ≤ -κ by linarith)
      simpa only [Real.rpow_neg hN0.le] using h
    · rw [show 600 * (N ^ κ) ^ 3 * N ^ (-20 * a) =
        600 * ((N ^ κ) ^ 3 * N ^ (-20 * a)) by ring, hgeom_eq]
      linarith
    · rw [hpal_eq, htime_eq]
      nlinarith
    · rw [hcost_eq]
      exact hc
  obtain ⟨R, hR⟩ := eventually_atTop.mp hev
  exact ⟨δ, hδ, hδε, κ, hκ, max 2 R, le_max_left _ _,
    fun N hN => hR N ((le_max_right _ _).trans hN)⟩

end Submission.Obl.k4_horizontal_three_traversal_spreading
