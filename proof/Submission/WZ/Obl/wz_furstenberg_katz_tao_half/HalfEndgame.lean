-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfEndgame.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfBridge
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.HalfNumerics

/-!
# `HalfEndgame`: the parallel-projection endgame at `s = 1/2`

`half_endgame_core` with `K = r ^ (-κ)`, `c = r ^ κ` and `κ = min (κ' / 100) (1 / 100)`,
where `κ'` is the gain of `dense_family_expansion` at `ε = 1/4`. The side conditions are
monomial comparisons `C r ^ a ≤ r ^ b` with `b < a`, true for small `r`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open SP

theorem half_endgame : HalfEndgame := by
  obtain ⟨κ', δ₀', hκ', hδ₀', _, hfam⟩ := exists_familyExpansionAt (1 / 4) (by norm_num)
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (κ' / 100) (1 / 100) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact lt_min (by positivity) (by norm_num)
  have hκκ' : 100 * κ ≤ κ' := by
    have := min_le_left (κ' / 100) (1 / 100)
    rw [hκdef]
    linarith
  have hκ1 : κ ≤ 1 / 100 := by rw [hκdef]; exact min_le_right _ _
  set C₀ : ℝ := 225 * (6600 * 16384) ^ 2 with hC₀
  set s2 : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ) with hs2
  have hC₀p : 0 < C₀ := by rw [hC₀]; positivity
  have hs2p : 0 < s2 := by rw [hs2]; positivity
  have hs2sq : s2 ^ 2 = 2 := by
    rw [hs2, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hprod : (1 - 2 * κ) * κ' > 12 * κ + κ := by nlinarith
  -- the monomial bounds
  obtain ⟨d1, hd1, _, hb1⟩ := exists_monomial_bound 512 (a := 1) (b := κ) (by linarith)
  obtain ⟨d2, hd2, _, hb2⟩ :=
    exists_monomial_bound (16384 / δ₀') (a := 1 - 2 * κ) (b := 0) (by linarith)
  obtain ⟨d3, hd3, _, hb3⟩ := exists_monomial_bound (32 * (C₀ * s2) * (16384 : ℝ) ^ κ')
    (a := -(25 / 2 * κ)) (b := (1 - 2 * κ) * (-κ')) (by nlinarith)
  obtain ⟨d4, hd4, _, hb4⟩ := exists_monomial_bound (6 * (16384 : ℝ) ^ κ')
    (a := -κ) (b := (1 - 2 * κ) * (-κ')) (by nlinarith)
  obtain ⟨d5, hd5, _, hb5⟩ := exists_monomial_bound (s2 * (16384 : ℝ) ^ (1 / 2 + κ'))
    (a := -κ - 1 / 2) (b := (1 - 2 * κ) * (-(1 / 2) - κ')) (by nlinarith)
  obtain ⟨d6, hd6, _, hb6⟩ := exists_monomial_bound ((16384 : ℝ) ^ κ' * 2 * C₀)
    (a := (1 - 2 * κ) * κ' + (-(2 * κ) - 1)) (b := 10 * κ - 1) (by nlinarith)
  obtain ⟨d7, hd7, _, hb7⟩ := exists_monomial_bound (4 * s2 * (16384 : ℝ) ^ κ' * (C₀ * s2) + 1)
    (a := -κ - 1 / 2) (b := (1 - 2 * κ) * (-κ') + (11 * κ - 1 / 2)) (by nlinarith)
  refine ⟨κ, min (min (min d1 d2) (min d3 d4)) (min (min d5 d6) (min d7 1)), hκ,
    by positivity, ?_⟩
  intro r hr hrr n p₀ p₁ p₂ H Q D Qh hcfg
  have hr1 : r ≤ d1 := hrr.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hr2 : r ≤ d2 := hrr.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hr3 : r ≤ d3 := hrr.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr4 : r ≤ d4 := hrr.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr5 : r ≤ d5 := hrr.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hr6 : r ≤ d6 := hrr.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hr7 : r ≤ d7 := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrone : r ≤ 1 := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have h256 : ∀ a : ℝ, (16384 : ℝ) ^ a * (16384 : ℝ) ^ (-a) = 1 := by
    intro a
    rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
  have hrp : ∀ a : ℝ, 0 < r ^ a := fun a => Real.rpow_pos_of_pos hr a
  have h256p : ∀ a : ℝ, 0 < (16384 : ℝ) ^ a := fun a => by positivity
  refine half_endgame_core hfam hcfg hr (hrp κ) (Real.rpow_le_one hr.le hrone hκ.le) ?_
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hrone (by linarith))
    rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · -- 64 r ≤ c / 8
    have h := hb1 r hr hr1
    rw [Real.rpow_one] at h
    linarith
  · -- δ ≤ δ₀'
    rw [cf_delta hr]
    have h := hb2 r hr hr2
    rw [Real.rpow_zero, div_mul_eq_mul_div, div_le_one hδ₀'] at h
    exact h
  · -- CA ≤ δ ^ (-κ')
    rw [cf_M hr, cf_Lg hr, cf_Kb hr, cf_La hr, cf_CA hr, cf_delta hr, cf_delta_rpow hr]
    have h := hb3 r hr hr3
    have h' := mul_le_mul_of_nonneg_left h (h256p (-κ')).le
    calc 32 * (C₀ * s2) * r ^ (-(25 / 2 * κ)) =
        (16384 : ℝ) ^ (-κ') * (32 * (C₀ * s2) * (16384 : ℝ) ^ κ' * r ^ (-(25 / 2 * κ))) := by
          have := h256 κ'
          rw [mul_comm ((16384 : ℝ) ^ κ') _] at this
          linear_combination (-(32 * (C₀ * s2) * r ^ (-(25 / 2 * κ)))) * this
      _ ≤ (16384 : ℝ) ^ (-κ') * r ^ ((1 - 2 * κ) * -κ') := h'
  · -- 6 K ≤ δ ^ (-κ')
    rw [cf_delta hr, cf_delta_rpow hr]
    have h := hb4 r hr hr4
    have h' := mul_le_mul_of_nonneg_left h (h256p (-κ')).le
    calc 6 * r ^ (-κ) = (16384 : ℝ) ^ (-κ') * (6 * (16384 : ℝ) ^ κ' * r ^ (-κ)) := by
          have := h256 κ'
          rw [mul_comm ((16384 : ℝ) ^ κ') _] at this
          linear_combination (-(6 * r ^ (-κ))) * this
      _ ≤ (16384 : ℝ) ^ (-κ') * r ^ ((1 - 2 * κ) * -κ') := h'
  · -- Kb ≤ δ ^ (-(1/2) - κ')
    rw [cf_Kb hr, cf_delta hr, cf_delta_rpow hr]
    have h := hb5 r hr hr5
    have h' := mul_le_mul_of_nonneg_left h (h256p (-(1 / 2) - κ')).le
    have e : (16384 : ℝ) ^ (1 / 2 + κ') * (16384 : ℝ) ^ (-(1 / 2) - κ') = 1 := by
      rw [← Real.rpow_add (by norm_num)]
      norm_num
    calc s2 * r ^ (-κ - 1 / 2) =
        (16384 : ℝ) ^ (-(1 / 2) - κ') * (s2 * (16384 : ℝ) ^ (1 / 2 + κ') * r ^ (-κ - 1 / 2)) := by
          rw [mul_comm ((16384 : ℝ) ^ (1 / 2 + κ')) _] at e
          linear_combination (-(s2 * r ^ (-κ - 1 / 2))) * e
      _ ≤ (16384 : ℝ) ^ (-(1 / 2) - κ') * r ^ ((1 - 2 * κ) * (-(1 / 2) - κ')) := h'
  · -- δ ^ κ' * Kb ^ 2 ≤ Lg
    rw [cf_M hr, cf_Lg hr, cf_Kb hr, cf_delta hr, cf_delta_rpow hr]
    have h := hb6 r hr hr6
    have hKb2 : (s2 * r ^ (-κ - 1 / 2)) ^ 2 = 2 * r ^ (-(2 * κ) - 1) := by
      rw [mul_pow, hs2sq, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      congr 2
      push_cast
      ring
    rw [hKb2, le_div_iff₀ hC₀p]
    have e : (16384 : ℝ) ^ κ' * r ^ ((1 - 2 * κ) * κ') * (2 * r ^ (-(2 * κ) - 1)) * C₀ =
        (16384 : ℝ) ^ κ' * 2 * C₀ * r ^ ((1 - 2 * κ) * κ' + (-(2 * κ) - 1)) := by
      rw [Real.rpow_add hr]
      ring
    rw [e]
    exact h
  · -- 4 Kb < δ ^ (-κ') * La
    rw [cf_M hr, cf_Lg hr, cf_Kb hr, cf_La hr, cf_delta hr, cf_delta_rpow hr]
    have h := hb7 r hr hr7
    have hpos := hrp (-κ - 1 / 2)
    have hlt : (4 * s2 * (16384 : ℝ) ^ κ' * (C₀ * s2)) * r ^ (-κ - 1 / 2) <
        r ^ ((1 - 2 * κ) * -κ' + (11 * κ - 1 / 2)) := by
      linarith
    rw [Real.rpow_add hr] at hlt
    have hCs : 0 < C₀ * s2 := mul_pos hC₀p hs2p
    rw [mul_div_assoc', lt_div_iff₀ hCs]
    have e1 : (16384 : ℝ) ^ (-κ') * (16384 : ℝ) ^ κ' = 1 := by
      rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
    have h' := mul_lt_mul_of_pos_left hlt (h256p (-κ'))
    calc 4 * (s2 * r ^ (-κ - 1 / 2)) * (C₀ * s2) =
        (16384 : ℝ) ^ (-κ') * (4 * s2 * (16384 : ℝ) ^ κ' * (C₀ * s2) * r ^ (-κ - 1 / 2)) := by
          linear_combination (-(4 * (s2 * r ^ (-κ - 1 / 2)) * (C₀ * s2))) * e1
      _ < (16384 : ℝ) ^ (-κ') * (r ^ ((1 - 2 * κ) * -κ') * r ^ (11 * κ - 1 / 2)) := h'
      _ = (16384 : ℝ) ^ (-κ') * r ^ ((1 - 2 * κ) * -κ') * r ^ (11 * κ - 1 / 2) := by ring

/-- The fixed-exponent bush estimate at `s = 1/2`, given the extraction. -/
theorem half_core_of_extraction (hE : HalfExtraction) :
    ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → KatzTaoFurstenbergAt r (1 / 2) ε₀ η :=
  half_core hE half_endgame

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
