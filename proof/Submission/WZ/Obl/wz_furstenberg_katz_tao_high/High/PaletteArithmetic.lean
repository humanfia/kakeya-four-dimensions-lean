-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.PaletteArithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/TopLevel.lean (95ffa93), Palette section.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Leaves

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

section Palette

variable {r : ℝ} {n : ℕ}

theorem palBase_pos (hr : 0 < r) : 0 < palBase r n := Real.rpow_pos_of_pos hr _

theorem palBase_gt_one (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n) : 1 < palBase r n := by
  unfold palBase
  apply Real.one_lt_rpow_of_pos_of_lt_one_of_neg hr hr1
  have : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < 1 / (n : ℝ) := by positivity
  linarith

theorem palBase_pow_n (hr : 0 < r) (hn : 0 < n) : palBase r n ^ (-(n : ℝ)) = r := by
  unfold palBase
  rw [← Real.rpow_mul hr.le]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h : -(1 / (n : ℝ)) * -(n : ℝ) = 1 := by field_simp
  rw [h, Real.rpow_one]

theorem rpow_eq_palBase (hr : 0 < r) (hn : 0 < n) (x : ℝ) :
    r ^ x = palBase r n ^ (-(n : ℝ) * x) := by
  rw [Real.rpow_mul (palBase_pos hr).le, palBase_pow_n hr hn]

theorem logb_palBase_rpow (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n) (x : ℝ) :
    Real.logb (palBase r n) (r ^ x) = -(n : ℝ) * x := by
  rw [rpow_eq_palBase hr hn x, Real.logb_rpow (palBase_pos hr)
    (palBase_gt_one hr hr1 hn).ne']

theorem r_le_palScale (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n) {i : ℕ} (hi : i ≤ n) :
    r ≤ palScale r n i := by
  unfold palScale
  calc r = palBase r n ^ (-(n : ℝ)) := (palBase_pow_n hr hn).symm
    _ ≤ palBase r n ^ (-(i : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (palBase_gt_one hr hr1 hn).le (by
          have : (i : ℝ) ≤ n := by exact_mod_cast hi
          linarith)

theorem palScale_pos (hr : 0 < r) (i : ℕ) : 0 < palScale r n i :=
  Real.rpow_pos_of_pos (palBase_pos hr) _

theorem palScale_antitone (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n)
    {i j : ℕ} (hij : i ≤ j) : palScale r n j ≤ palScale r n i := by
  apply Real.rpow_le_rpow_of_exponent_le (palBase_gt_one hr hr1 hn).le
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

theorem palScale_le_inv_base (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n)
    {i : ℕ} (hi : 0 < i) : palScale r n i ≤ (palBase r n)⁻¹ := by
  have hh := palScale_antitone hr hr1 hn hi
  simpa only [palScale, Nat.cast_one, Real.rpow_neg_one] using hh

/-- For a fixed finite palette, shrinking the fine scale makes its base
larger than any prescribed constant. -/
theorem exists_palBase_cutoff {A : ℝ} (hA : 1 < A) (hn : 0 < n) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 4 ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → A ≤ palBase r n := by
  refine ⟨min (1 / 4) (A ^ (-(n : ℝ))), by positivity, min_le_left _ _, ?_⟩
  intro r hr hsmall
  have hpow := Real.rpow_le_rpow_of_nonpos hr
    (hsmall.trans (min_le_right _ _))
    (show -(1 / (n : ℝ)) ≤ 0 by exact neg_nonpos.mpr (by positivity))
  have heq : (A ^ (-(n : ℝ))) ^ (-(1 / (n : ℝ))) = A := by
    rw [← Real.rpow_mul (by linarith : 0 ≤ A)]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [show -(n : ℝ) * -(1 / (n : ℝ)) = 1 by field_simp, Real.rpow_one]
  exact heq ▸ hpow

/-- `log_B X ≤ θ n` once `r ≤ exp (-(log X) / θ)`. -/
theorem logb_palBase_le (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n) {X θ : ℝ} (hX : 1 ≤ X)
    (hθ : 0 < θ) (hrθ : r ≤ Real.exp (-(Real.log X / θ))) :
    Real.logb (palBase r n) X ≤ θ * n := by
  have hlogr : Real.log r ≤ -(Real.log X / θ) := by
    have := Real.log_le_log hr hrθ
    rwa [Real.log_exp] at this
  have hlogB : Real.log (palBase r n) = -(1 / (n : ℝ)) * Real.log r := by
    unfold palBase; rw [Real.log_rpow hr]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogBpos : 0 < Real.log (palBase r n) := Real.log_pos (palBase_gt_one hr hr1 hn)
  unfold Real.logb
  rw [div_le_iff₀ hlogBpos, hlogB]
  have h1 : θ * n * (-(1 / (n : ℝ)) * Real.log r) = θ * (-Real.log r) := by
    field_simp
  rw [h1]
  have h2 : Real.log X / θ ≤ -Real.log r := by linarith
  calc Real.log X = θ * (Real.log X / θ) := by field_simp
    _ ≤ θ * (-Real.log r) := mul_le_mul_of_nonneg_left h2 hθ.le

theorem logb_le_logb_900 {B X : ℝ} (hB : 1 < B) (hX : 0 < X) (hX9 : X ≤ 900) :
    Real.logb B X ≤ Real.logb B 900 :=
  Real.logb_le_logb_of_le hB hX hX9

end Palette

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
