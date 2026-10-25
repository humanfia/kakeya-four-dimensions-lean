-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.RichNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PowerBudget

/-!
# Numerics of `half_rich_class`

`scales_le_rpow`: the number `L + 1` of dyadic scales with `2 ^ L ≤ 128 / r` is at most
`r ^ (-2 c)` for small `r` (Bernoulli's inequality for `2 ^ c`).

`rich_numerics`: for `0 < ε₀, η ≤ 1/1000` and small `r`, the six inequalities used in the
assembly of `half_rich_class` (all of the form `constant ≤ r ^ (-γ)` with `γ > 0`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

theorem scales_le_rpow {c : ℝ} (hc : 0 < c) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ ∀ r : ℝ, 0 < r → r ≤ r₂ → ∀ L : ℕ, (2 : ℝ) ^ L ≤ 128 / r →
      ((L : ℝ) + 1) ≤ r ^ (-(2 * c)) := by
  set a : ℝ := (2 : ℝ) ^ c - 1 with ha
  have ha0 : 0 < a := by
    have : (1 : ℝ) < 2 ^ c := Real.one_lt_rpow (by norm_num) hc
    linarith
  obtain ⟨r₂, hr₂, hr₂1, hbound⟩ := exists_power_bound ((128 : ℝ) ^ c * (1 / a + 1)) hc
  refine ⟨r₂, hr₂, ?_⟩
  intro r hr hrr L hL
  have hbern : 1 + (L : ℝ) * a ≤ (1 + a) ^ L := one_add_mul_le_pow (by linarith) L
  have h1a : 1 + a = (2 : ℝ) ^ c := by rw [ha]; ring
  rw [h1a] at hbern
  have hpow : ((2 : ℝ) ^ c) ^ L = ((2 : ℝ) ^ L) ^ c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2 : ℝ),
      ← Real.rpow_mul (by norm_num), mul_comm]
  rw [hpow] at hbern
  have h128 : ((2 : ℝ) ^ L) ^ c ≤ (128 / r) ^ c :=
    Real.rpow_le_rpow (by positivity) hL hc.le
  have hge1 : (1 : ℝ) ≤ (128 / r) ^ c := by
    have : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
    exact Real.one_le_rpow (by linarith) hc.le
  have hL1 : (L : ℝ) ≤ (128 / r) ^ c / a := by
    rw [le_div_iff₀ ha0]; linarith
  have hsplit : (128 / r) ^ c = (128 : ℝ) ^ c * r ^ (-c) := by
    rw [Real.div_rpow (by norm_num) hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
  have hC := hbound r hr hrr
  calc ((L : ℝ) + 1) ≤ (128 / r) ^ c / a + (128 / r) ^ c := by linarith
    _ = (128 : ℝ) ^ c * (1 / a + 1) * r ^ (-c) := by rw [hsplit]; field_simp
    _ ≤ r ^ (-c) * r ^ (-c) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hr.le _)
    _ = r ^ (-(2 * c)) := by rw [← Real.rpow_add hr]; congr 1; ring

/-- `C ≤ r ^ (-s)` from a power bound, in the form `C * r ^ a ≤ r ^ b` with `a - b = s`. -/
theorem mul_rpow_le_of_bound {r C a b s : ℝ} (hr : 0 < r) (hC : C ≤ r ^ (-s)) (hab : b = a - s) :
    C * r ^ a ≤ r ^ b := by
  have hra : 0 < r ^ a := Real.rpow_pos_of_pos hr a
  calc C * r ^ a ≤ r ^ (-s) * r ^ a := mul_le_mul_of_nonneg_right hC hra.le
    _ = r ^ b := by rw [← Real.rpow_add hr, hab]; congr 1; ring

theorem rich_numerics {ε₀ η : ℝ} (hε₀ : 0 < ε₀) (hη : 0 < η) (hε₀1 : ε₀ ≤ 1 / 1000)
    (hη1 : η ≤ 1 / 1000) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r ≤ r₁ →
      r ≤ 1 / 100 ∧
      52 * r ≤ r ^ (20 * (ε₀ + η)) ∧
      10 ^ 6 * r ^ (-2 - 4 * η) * (r ^ (20 * (ε₀ + η))) ^ (1 / 2 : ℝ) ≤
        r ^ (4 * η + ε₀ - 2) / 4 ∧
      r ^ (-1 + 200 * (ε₀ + η)) ≤ 3 / 369664 * r ^ (8 * η + 2 * ε₀ - 1) ∧
      (∀ L : ℕ, (2 : ℝ) ^ L ≤ 128 / r →
        152 * ((L : ℝ) + 1) * (16 * Real.sqrt 20 * 10 ^ 6 * ((L : ℝ) + 1) * (8 / 3) *
          r ^ (-(10 * η) - ε₀)) * r ^ (-η) ≤ r ^ (-(100 * (ε₀ + η)))) ∧
      r ^ (-1 + 100 * (ε₀ + η)) * (12 * 52 ^ (1 / 2 : ℝ) * r ^ (-2 * η) *
        (r ^ (20 * (ε₀ + η))) ^ (-(1 / 2) : ℝ)) ≤ 3 / 128 * r ^ (5 * η + ε₀ - 1) := by
  set κ := ε₀ + η with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨a₂, ha₂, ha₂1, h₂⟩ := exists_power_bound 52 (s := 1 - 20 * κ) (by linarith)
  obtain ⟨a₃, ha₃, ha₃1, h₃⟩ := exists_power_bound (4 * 10 ^ 6) (s := 2 * η + 9 * ε₀)
    (by positivity)
  obtain ⟨a₄, ha₄, ha₄1, h₄⟩ := exists_power_bound (369664 / 3) (s := 192 * η + 198 * ε₀)
    (by positivity)
  obtain ⟨a₅, ha₅, h₅⟩ := scales_le_rpow (c := κ) hκ0
  obtain ⟨a₅', ha₅', ha₅'1, h₅'⟩ :=
    exists_power_bound (152 * (16 * Real.sqrt 20 * 10 ^ 6 * (8 / 3))) (s := 85 * η + 95 * ε₀)
    (by positivity)
  obtain ⟨a₆, ha₆, ha₆1, h₆⟩ := exists_power_bound (128 / 3 * (12 * 52 ^ (1 / 2 : ℝ)))
    (s := 83 * η + 89 * ε₀) (by positivity)
  refine ⟨min (1 / 100) (min a₂ (min a₃ (min a₄ (min a₅ (min a₅' a₆))))), by positivity, ?_⟩
  intro r hr hrr
  have hr2 : r ≤ a₂ := (hrr.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hr3 : r ≤ a₃ := ((hrr.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_left _ _)
  have hr4 : r ≤ a₄ := (((hrr.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hr5 : r ≤ a₅ := ((((hrr.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hr5' : r ≤ a₅' := (((((hrr.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_left _ _)
  have hr6 : r ≤ a₆ := (((((hrr.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)
  have hhalf : ∀ x : ℝ, (r ^ x) ^ (1 / 2 : ℝ) = r ^ (x / 2) := by
    intro x; rw [← Real.rpow_mul hr.le]; congr 1; ring
  have hnhalf : ∀ x : ℝ, (r ^ x) ^ (-(1 / 2) : ℝ) = r ^ (-(x / 2)) := by
    intro x; rw [← Real.rpow_mul hr.le]; congr 1; ring
  refine ⟨hrr.trans (min_le_left _ _), ?_, ?_, ?_, ?_, ?_⟩
  · -- 52 r ≤ r ^ (20 κ)
    have := mul_rpow_le_of_bound (a := 1) (b := 20 * κ) hr (h₂ r hr hr2) (by ring)
    rwa [Real.rpow_one] at this
  · rw [hhalf]
    have h := mul_rpow_le_of_bound (a := -2 - 4 * η + 10 * κ) (b := 4 * η + ε₀ - 2) hr
      (h₃ r hr hr3) (by rw [hκ]; ring)
    have e1 : r ^ (-2 - 4 * η) * r ^ (20 * κ / 2) = r ^ (-2 - 4 * η + 10 * κ) := by
      rw [← Real.rpow_add hr]; congr 1; ring
    rw [mul_assoc, e1]
    linarith
  · have h := mul_rpow_le_of_bound (a := -1 + 200 * κ) (b := 8 * η + 2 * ε₀ - 1) hr
      (h₄ r hr hr4) (by rw [hκ]; ring)
    linarith
  · intro L hL
    have hL' := h₅ r hr hr5 L hL
    have hL0 : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
    have hsq : ((L : ℝ) + 1) * ((L : ℝ) + 1) ≤ r ^ (-(2 * κ)) * r ^ (-(2 * κ)) :=
      mul_le_mul hL' hL' hL0 (Real.rpow_nonneg hr.le _)
    have hK := h₅' r hr hr5'
    have hpos : 0 < r ^ (-(10 * η) - ε₀) * r ^ (-η) := by positivity
    calc 152 * ((L : ℝ) + 1) * (16 * Real.sqrt 20 * 10 ^ 6 * ((L : ℝ) + 1) * (8 / 3) *
          r ^ (-(10 * η) - ε₀)) * r ^ (-η)
        = (152 * (16 * Real.sqrt 20 * 10 ^ 6 * (8 / 3))) * (((L : ℝ) + 1) * ((L : ℝ) + 1)) *
            (r ^ (-(10 * η) - ε₀) * r ^ (-η)) := by ring
      _ ≤ r ^ (-(85 * η + 95 * ε₀)) * (r ^ (-(2 * κ)) * r ^ (-(2 * κ))) *
            (r ^ (-(10 * η) - ε₀) * r ^ (-η)) := by gcongr
      _ = r ^ (-(100 * (ε₀ + η))) := by
          rw [← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr]
          congr 1; rw [hκ]; ring
  · rw [hnhalf]
    have h := h₆ r hr hr6
    have hfold : r ^ (-1 + 100 * κ) * r ^ (-2 * η) * r ^ (-(20 * κ / 2)) =
        r ^ (5 * η + ε₀ - 1) * r ^ (83 * η + 89 * ε₀) := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr]; congr 1; rw [hκ]; ring
    have hq : 0 < r ^ (83 * η + 89 * ε₀) := Real.rpow_pos_of_pos hr _
    have hp : 0 < r ^ (5 * η + ε₀ - 1) := Real.rpow_pos_of_pos hr _
    have hinv : r ^ (-(83 * η + 89 * ε₀)) * r ^ (83 * η + 89 * ε₀) = 1 := by
      rw [← Real.rpow_add hr]; simp
    have h' : 128 / 3 * (12 * 52 ^ (1 / 2 : ℝ)) * r ^ (83 * η + 89 * ε₀) ≤ 1 := by
      calc 128 / 3 * (12 * 52 ^ (1 / 2 : ℝ)) * r ^ (83 * η + 89 * ε₀)
          ≤ r ^ (-(83 * η + 89 * ε₀)) * r ^ (83 * η + 89 * ε₀) :=
            mul_le_mul_of_nonneg_right h hq.le
        _ = 1 := hinv
    have h'' : 12 * 52 ^ (1 / 2 : ℝ) * r ^ (83 * η + 89 * ε₀) ≤ 3 / 128 := by
      nlinarith
    calc r ^ (-1 + 100 * κ) * (12 * 52 ^ (1 / 2 : ℝ) * r ^ (-2 * η) * r ^ (-(20 * κ / 2)))
        = (12 * 52 ^ (1 / 2 : ℝ)) * (r ^ (-1 + 100 * κ) * r ^ (-2 * η) * r ^ (-(20 * κ / 2))) := by
          ring
      _ = (12 * 52 ^ (1 / 2 : ℝ) * r ^ (83 * η + 89 * ε₀)) * r ^ (5 * η + ε₀ - 1) := by
          rw [hfold]; ring
      _ ≤ 3 / 128 * r ^ (5 * η + ε₀ - 1) := mul_le_mul_of_nonneg_right h'' hp.le

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
