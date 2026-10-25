-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_balanced_refinement.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Basic

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_balanced_refinement

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- Fixed-depth losses can be absorbed by a positive power of the bottom radius. -/
theorem choose_parameters (B : ℕ) (ε C : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ (θ : ℝ) (q : ℕ) (d₀ : ℝ),
      0 < θ ∧ θ ≤ ε / 2 ∧ θ ≤ 1 ∧ 0 < q ∧ 4 < ε * q ∧ 0 < d₀ ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ → C * d < 1 ∧ d ^ (ε / 2) * (q : ℝ) ^ (B + 1) ≤ 1 := by
  obtain ⟨q, hq⟩ := exists_nat_gt (max (4 / ε) 0)
  have hqpos : 0 < q := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hq)
  have hεq : 4 < ε * q := by
    have h := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_left _ _) hq)
    nlinarith
  let W : ℝ := (q : ℝ) ^ (B + 1)
  have hW : 0 < W := pow_pos (by exact_mod_cast hqpos) _
  let D : ℝ := W ^ (-2 / ε)
  have hD : 0 < D := Real.rpow_pos_of_pos hW _
  have hDp : D ^ (ε / 2) = W⁻¹ := by
    dsimp [D]
    rw [← Real.rpow_mul hW.le]
    have he : (-2 / ε) * (ε / 2) = -1 := by field_simp
    rw [he, Real.rpow_neg_one]
  refine ⟨min (ε / 2) 1, q, min (1 / (C + 1)) D,
    lt_min (by positivity) one_pos, min_le_left _ _, min_le_right _ _, hqpos, hεq,
    lt_min (by positivity) hD, ?_⟩
  intro d hd hdd
  constructor
  · calc
      C * d ≤ C * (1 / (C + 1)) :=
        mul_le_mul_of_nonneg_left (hdd.trans (min_le_left _ _)) hC
      _ = C / (C + 1) := by ring
      _ < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  · calc
      d ^ (ε / 2) * (q : ℝ) ^ (B + 1) ≤ D ^ (ε / 2) * W :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hd.le (hdd.trans (min_le_right _ _)) (by positivity)) hW.le
      _ = 1 := by rw [hDp, inv_mul_cancel₀ hW.ne']

/-- The bottom Katz--Tao count bounds the number of bins independently of the radius. -/
theorem cardinal_lt_power {d θ ε C : ℝ} {q n : ℕ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : θ ≤ 1) (hC : 0 ≤ C)
    (hCd : C * d < 1) (hq : 4 < ε * q)
    (hcount : (n : ℝ) * d ^ 2 ≤ d ^ (-θ) * C) :
    (n : ℝ) < (d ^ (-ε)) ^ q := by
  have hp : d ^ (-θ) ≤ d⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθ)
  have hc : (n : ℝ) * d ^ 2 ≤ d⁻¹ * C :=
    hcount.trans (mul_le_mul_of_nonneg_right hp hC)
  have hc3 : (n : ℝ) * d ^ 3 ≤ C := by
    have h := mul_le_mul_of_nonneg_right hc hd.le
    have he : d⁻¹ * C * d = C := by field_simp
    rw [he] at h
    nlinarith
  have hc4 : (n : ℝ) * d ^ 4 < 1 := by
    have h := mul_le_mul_of_nonneg_right hc3 hd.le
    nlinarith
  have hn : (n : ℝ) < (d ^ 4)⁻¹ := by
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ (pow_pos hd 4)).mpr hc4
  apply hn.trans_le
  rw [← Real.rpow_mul_natCast hd.le]
  have h := Real.rpow_le_rpow_of_exponent_ge hd hd1 (show -ε * (q : ℝ) ≤ -(4 : ℝ) by nlinarith)
  simpa only [Real.rpow_neg hd.le, Real.rpow_ofNat] using h

lemma retained_mass {d ε : ℝ} {q B J : ℕ} {a b : ℝ≥0∞}
    (hd : 0 < d) (hq : 0 < q) (hJB : J ≤ B)
    (hloss : d ^ (ε / 2) * (q : ℝ) ^ (B + 1) ≤ 1)
    (hmass : a ≤ (q : ℝ≥0∞) ^ (J + 1) * b) :
    ENNReal.ofReal (d ^ (ε / 2)) * a ≤ b := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow : (q : ℝ) ^ (J + 1) ≤ (q : ℝ) ^ (B + 1) :=
    pow_le_pow_right₀ hq1 (by omega)
  have hreal : d ^ (ε / 2) * (q : ℝ) ^ (J + 1) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hd.le _)).trans hloss
  have hcoef : ENNReal.ofReal (d ^ (ε / 2)) * (q : ℝ≥0∞) ^ (J + 1) ≤ 1 := by
    have h := ENNReal.ofReal_le_ofReal hreal
    simpa only [ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _), ENNReal.ofReal_pow
      (Nat.cast_nonneg q), ENNReal.ofReal_natCast, ENNReal.ofReal_one] using h
  calc
    ENNReal.ofReal (d ^ (ε / 2)) * a ≤
        ENNReal.ofReal (d ^ (ε / 2)) * ((q : ℝ≥0∞) ^ (J + 1) * b) :=
      mul_le_mul' le_rfl hmass
    _ = (ENNReal.ofReal (d ^ (ε / 2)) * (q : ℝ≥0∞) ^ (J + 1)) * b := by rw [mul_assoc]
    _ ≤ 1 * b := mul_le_mul' hcoef le_rfl
    _ = b := one_mul b

end WangZahlLot.Obl.wz_tower_balanced_refinement
