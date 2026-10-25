-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/WindowNumerics.lean (bf60247).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CoarseCount
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeUpper
import Submission.WZ.Obl.wz_move_two_prism_fan_avoidance.Coloring

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

/-- The explicit geometric coefficient of the pin Cauchy--Schwarz estimate. -/
noncomputable def pinRatioConst : ℝ := 128000 * (64 * 26 + 2) * (36 * 26 + 2)

/-- The pin estimate costs only three logarithms, in addition to its
normalized point Frostman constant. -/
theorem pinConst_le_log {r w C A : ℝ} {KY : ℕ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hrw : r ≤ w) (hw2 : 26 * w ≤ 1 / 2)
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hKY : (KY : ℝ) + 1 ≤ A * (Real.logb 2 (1 / r) + 2)) :
    pinConst w C KY ≤ pinRatioConst * A ^ 2 * C * (Real.logb 2 (1 / r) + 2) ^ 3 := by
  have hw : 0 < w := hr.trans_le hrw
  have hlogr : 0 ≤ Real.log (1 / r) := Real.log_nonneg ((one_le_div hr).mpr hr1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog21 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlogbr : 0 ≤ Real.logb 2 (1 / r) := by
    unfold Real.logb
    exact div_nonneg hlogr hlog2.le
  have hlogr' : Real.log (1 / r) ≤ Real.logb 2 (1 / r) := by
    unfold Real.logb
    rw [le_div_iff₀ hlog2]
    nlinarith
  have harg : 1 / (26 * w) ≤ 1 / r := by
    apply one_div_le_one_div_of_le hr
    linarith
  have hlogw : Real.log (1 / (26 * w)) ≤ Real.logb 2 (1 / r) :=
    (Real.log_le_log (by positivity) harg).trans hlogr'
  have hlogw0 : 0 ≤ Real.log (1 / (26 * w)) := by
    apply Real.log_nonneg
    rw [one_le_div (by positivity)]
    linarith
  have hlog : 1 + Real.log (1 / (26 * w)) ≤ Real.logb 2 (1 / r) + 2 := by linarith
  have hRat : 0 ≤ pinRatioConst := by unfold pinRatioConst; positivity
  have hid : pinConst w C KY = pinRatioConst * C *
      (1 + Real.log (1 / (26 * w))) * ((KY : ℝ) + 1) ^ 2 := by
    unfold pinConst pinRatioConst
    field_simp
  rw [hid]
  calc
    _ ≤ pinRatioConst * C * (Real.logb 2 (1 / r) + 2) *
        (A * (Real.logb 2 (1 / r) + 2)) ^ 2 := by gcongr
    _ = _ := by ring

/-- Uniform absorption of all logarithms in the pin estimate. -/
theorem pinConst_small_power {ν A : ℝ} (hν : 0 < ν) (hA : 1 ≤ A) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r w u C : ℝ, ∀ KY : ℕ,
      0 < r → r ≤ r₀ → r ≤ w → 26 * w ≤ 1 / 2 → 0 ≤ C → C ≤ r ^ (-u) →
      (KY : ℝ) + 1 ≤ A * (Real.logb 2 (1 / r) + 2) →
      pinConst w C KY ≤ r ^ (-u - ν) := by
  let H : ℝ := pinRatioConst * A ^ 2
  have hH : 1 ≤ H := by
    have hRat : 1 ≤ pinRatioConst := by unfold pinRatioConst; norm_num
    have hA2 : 1 ≤ A ^ 2 := one_le_pow₀ hA
    exact one_le_mul_of_one_le_of_one_le hRat hA2
  obtain ⟨r₀, hr₀, hr₀1, hsmall⟩ :=
    WangZahlLot.Obl.wz_move_two_prism_fan_avoidance.small_delta_log
      (s := ν / 3) (C := H) (by positivity) (by linarith)
  refine ⟨r₀, hr₀, hr₀1, ?_⟩
  intro r w u C KY hr hrr hrw hw hC hCu hKY
  have hr1 := hrr.trans hr₀1
  set L : ℝ := Real.logb 2 (1 / r) + 2
  have hL : 0 ≤ L := by
    have hh : 0 ≤ Real.logb 2 (1 / r) := by
      unfold Real.logb
      exact div_nonneg (Real.log_nonneg ((one_le_div hr).mpr hr1))
        (Real.log_pos (by norm_num)).le
    dsimp [L]
    linarith
  have hHL : H * L ≤ r ^ (-(ν / 3)) := hsmall r hr hrr
  have hH3 : H ≤ H ^ 3 := by nlinarith [sq_nonneg (H - 1)]
  have hpow : H * L ^ 3 ≤ r ^ (-ν) := by
    calc H * L ^ 3 ≤ H ^ 3 * L ^ 3 := mul_le_mul_of_nonneg_right hH3 (pow_nonneg hL _)
      _ = (H * L) ^ 3 := (mul_pow _ _ _).symm
      _ ≤ (r ^ (-(ν / 3))) ^ (3 : ℕ) := by gcongr
      _ = r ^ (-ν) := by
        rw [← Real.rpow_mul_natCast hr.le]
        congr 1
        norm_num
  have hbase := pinConst_le_log hr hr1 hrw hw hC (by linarith) hKY
  calc pinConst w C KY ≤ H * C * L ^ 3 := hbase
    _ ≤ H * r ^ (-u) * L ^ 3 := by gcongr
    _ = r ^ (-u) * (H * L ^ 3) := by ring
    _ ≤ r ^ (-u) * r ^ (-ν) := by gcongr
    _ = r ^ (-u - ν) := by rw [← Real.rpow_add hr]; congr 1

/-- The complete coefficient in the window square bound has a loss linear
in the regularity, near-extremality, and two-endedness parameters. The
geometric constants are kept explicit for reuse with different charts. -/
theorem window_coefficient_le_power {r s ε ε₀ ℓ ν Cn AC Cp L : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hCn : 0 ≤ Cn) (hAC : 0 ≤ AC) (hCp : 0 ≤ Cp) (hL : 0 ≤ L)
    (hCpow : Cp ≤ r ^ (-2 * ε - ν)) (hLpow : L ≤ r ^ (-(2 * s) - ε₀)) :
    Cn ^ 3 * (r ^ (-ε)) ^ (4 : ℕ) * tubeConst r s ε (r ^ ℓ) (r ^ (-ε)) * Cp *
        ((r ^ (-ε)) ^ (2 : ℕ) * AC) ^ (2 : ℕ) * (2 * (49 * r ^ (-ε))) ^ (2 : ℕ) * L /
          (r ^ (ε - s)) ^ (2 : ℕ) ≤
      (5200 * Cn ^ 3 * AC ^ (2 : ℕ) * 98 ^ (2 : ℕ)) *
        r ^ (-(20 * ε + ε₀ + ℓ * s + ν)) := by
  have hquad := tubeConst_le_power (η := ε) (k := ε) (ℓ := ℓ) hr hr1 hs1 hε
  have hquad0 := tubeConst_nonneg (s := s) (η := ε) hr (Real.rpow_pos_of_pos hr ℓ)
    (Real.rpow_nonneg hr.le (-ε))
  calc
    _ ≤ Cn ^ 3 * (r ^ (-ε)) ^ (4 : ℕ) * (5200 * r ^ (-3 * ε - 3 * ε - ℓ * s)) *
        r ^ (-2 * ε - ν) * ((r ^ (-ε)) ^ (2 : ℕ) * AC) ^ (2 : ℕ) *
        (2 * (49 * r ^ (-ε))) ^ (2 : ℕ) * r ^ (-(2 * s) - ε₀) /
          (r ^ (ε - s)) ^ (2 : ℕ) := by gcongr
    _ = (5200 * Cn ^ 3 * AC ^ (2 : ℕ) * 98 ^ (2 : ℕ)) *
        ((r ^ (-ε)) ^ (10 : ℕ) * r ^ (-3 * ε - 3 * ε - ℓ * s) *
          r ^ (-2 * ε - ν) * r ^ (-(2 * s) - ε₀) / (r ^ (ε - s)) ^ (2 : ℕ)) := by ring
    _ = _ := by
      congr 1
      rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_mul_natCast hr.le,
        ← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_sub hr]
      congr 1
      norm_num
      ring

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- A failed configuration admits a dyadic counting range with a logarithmic
length controlled independently of the number of pins. -/
theorem FailData.pin_dyadic_range {r s ε₀ ε : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ ε P D) (hr1 : r ≤ 1) (hε : ε ≤ 1) :
    ∃ KY : ℕ, (P.card : ℝ) ≤ 2 ^ KY ∧
      (KY : ℝ) + 1 ≤ 2 * (Real.logb 2 (1 / r) + 2) := by
  have hr := h.r_pos
  have hP : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr h.P_ne
  have hP1 : (1 : ℝ) ≤ P.card := by exact_mod_cast Finset.card_pos.mpr h.P_ne
  have hpow : r ^ (-ε) ≤ 1 / r := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hcard : (P.card : ℝ) ≤ 4 * (1 / r) ^ (2 : ℕ) := by
    calc (P.card : ℝ) ≤ r ^ (-ε) * (4 / r) := h.P_card_le (by linarith)
      _ ≤ (1 / r) * (4 / r) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = _ := by ring
  have hlog0 : 0 ≤ Real.logb 2 (P.card : ℝ) := Real.logb_nonneg (by norm_num) hP1
  let KY := ⌈Real.logb 2 (P.card : ℝ)⌉₊
  have hupper : (P.card : ℝ) ≤ 2 ^ KY := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.le_ceil (Real.logb 2 (P.card : ℝ)))
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hP, Real.rpow_natCast] at hh
  have hlog : Real.logb 2 (P.card : ℝ) ≤ 2 + 2 * Real.logb 2 (1 / r) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hP hcard
    have h4 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [Real.logb_mul (by norm_num) (by positivity), h4, Real.logb_pow] at hh
    simpa using hh
  refine ⟨KY, hupper, ?_⟩
  have hh := Nat.ceil_lt_add_one hlog0
  dsimp [KY]
  linarith

/-- The normalized point constant in the pin estimate has loss `2ε`. -/
theorem FailData.normalized_point_coefficient {r s ε₀ ε : ℝ}
    {P : Finset E2} {D : Finset (E2 × E2)} (h : FailData r s ε₀ ε P D) :
    r ^ (-ε) / r / (P.card : ℝ) ≤ r ^ (-2 * ε) := by
  have hr := h.r_pos
  have hP : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr h.P_ne
  have hid : r ^ (-2 * ε) * r ^ (ε - 1) = r ^ (-ε) / r := by
    calc
      r ^ (-2 * ε) * r ^ (ε - 1) = r ^ (-ε - 1) := by
        rw [← Real.rpow_add hr]
        congr 1
        ring
      _ = r ^ (-ε) / r ^ (1 : ℝ) := Real.rpow_sub hr _ _
      _ = _ := by rw [Real.rpow_one]
  rw [div_le_iff₀ hP]
  calc r ^ (-ε) / r = r ^ (-2 * ε) * r ^ (ε - 1) := hid.symm
    _ ≤ r ^ (-2 * ε) * (P.card : ℝ) :=
      mul_le_mul_of_nonneg_left h.P_card (Real.rpow_nonneg hr.le _)

/-- A single dyadic range controls the pin estimate at every intermediate
tube width, with all geometric and logarithmic constants absorbed. -/
theorem fail_pinConst_small_power {ν : ℝ} (hν : 0 < ν) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ r s ε₀ ε : ℝ,
      ∀ (P : Finset E2) (D : Finset (E2 × E2)),
      FailData r s ε₀ ε P D → r ≤ r₀ → ε ≤ 1 →
      ∃ KY : ℕ, (P.card : ℝ) ≤ 2 ^ KY ∧ ∀ w : ℝ, r ≤ w → 26 * w ≤ 1 / 2 →
        pinConst w (r ^ (-ε) / r / (P.card : ℝ)) KY ≤ r ^ (-2 * ε - ν) := by
  obtain ⟨r₀, hr₀, hr₀1, hsmall⟩ := pinConst_small_power (A := 2) hν (by norm_num)
  refine ⟨r₀, hr₀, hr₀1, ?_⟩
  intro r s ε₀ ε P D h hrr hε
  obtain ⟨KY, hKY, hKYlog⟩ := h.pin_dyadic_range (hrr.trans hr₀1) hε
  refine ⟨KY, hKY, ?_⟩
  intro w hrw hw
  have hCY : 0 ≤ r ^ (-ε) / r / (P.card : ℝ) :=
    div_nonneg (div_nonneg (Real.rpow_nonneg h.r_pos.le _) h.r_pos.le) (Nat.cast_nonneg _)
  have hCpow : r ^ (-ε) / r / (P.card : ℝ) ≤ r ^ (-(2 * ε)) := by
    simpa only [neg_mul] using h.normalized_point_coefficient
  simpa only [neg_mul] using hsmall r w (2 * ε) (r ^ (-ε) / r / (P.card : ℝ)) KY
    h.r_pos hrr hrw hw hCY hCpow hKYlog

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
