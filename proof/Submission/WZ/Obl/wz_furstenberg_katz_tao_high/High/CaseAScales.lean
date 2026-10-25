-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CaseAScales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseANumerics

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

/-- A Case A window stays a fixed fraction away from both ends of the
palette, with constants independent of its length. -/
theorem caseA_window_indices {c L : ℝ} {n h a : ℕ}
    (hc : 0 < c) (hL : 1 ≤ L) (hn : 0 < n)
    (hna : (n : ℝ) ≤ L * a) (hah : (a : ℝ) ≤ 2 * h)
    (hgap : (h : ℝ) + c * a ≤ a) :
    0 < h ∧ h < a ∧ 1 / (2 * L) ≤ (h : ℝ) / n ∧
      c / L ≤ ((a : ℝ) - h) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 < L := by linarith
  have haR : (0 : ℝ) < a := by nlinarith only [hna, hnR, hL0]
  have hhR : (0 : ℝ) < h := by linarith only [haR, hah]
  have hhaR : (h : ℝ) < a := by nlinarith only [hgap, hc, haR]
  refine ⟨by exact_mod_cast hhR, by exact_mod_cast hhaR, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L) hnR]
    nlinarith only [hna, hah, hL0]
  · rw [div_le_div_iff₀ hL0 hnR]
    nlinarith only [hna, hgap, hL0, hc]

/-- Moving the fine end of the window one palette step leaves room for
coarse counting estimates that require the class width to exceed `r`. -/
theorem caseA_trim_window {c L : ℝ} {n h a : ℕ}
    (hc : 0 < c) (hL : 1 ≤ L) (hn : 0 < n) (han : a ≤ n)
    (hnL : 4 * L ≤ (n : ℝ)) (hnc : 4 * L / c ≤ (n : ℝ))
    (hna : (n : ℝ) ≤ L * a) (hah : (a : ℝ) ≤ 2 * h)
    (hgap : (h : ℝ) + c * a ≤ a) :
    h < a - 1 ∧ a - 1 < n ∧ (n : ℝ) ≤ (2 * L) * (a - 1 : ℕ) ∧
      ((a - 1 : ℕ) : ℝ) ≤ 2 * h ∧
      (h : ℝ) + (c / 2) * (a - 1 : ℕ) ≤ (a - 1 : ℕ) := by
  have hL0 : 0 < L := by linarith
  have ha4 : (4 : ℝ) ≤ a := by nlinarith only [hnL, hna, hL0]
  have ha1 : 1 ≤ a := by exact_mod_cast (show (1 : ℝ) ≤ a by linarith)
  have hca : 4 ≤ c * a := by
    have hh := (div_le_iff₀ hc).mp hnc
    nlinarith only [hh, hna, hL0, hc]
  have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha1, Nat.cast_one]
  have hha : (h : ℝ) < (a - 1 : ℕ) := by rw [hcast]; linarith only [hgap, hca]
  refine ⟨by exact_mod_cast hha, by omega, ?_, ?_, ?_⟩
  · rw [hcast]
    nlinarith only [hna, ha4, hL0]
  · rw [hcast]
    linarith only [hah]
  · rw [hcast]
    nlinarith only [hgap, hca, hc]

/-- The physical tube and model scales of a Case A window. -/
theorem caseA_window_scales {r c L : ℝ} {n h a : ℕ}
    (hr : 0 < r) (hr1 : r < 1) (hc : 0 < c) (hL : 1 ≤ L) (hn : 0 < n)
    (hna : (n : ℝ) ≤ L * a) (hah : (a : ℝ) ≤ 2 * h)
    (hgap : (h : ℝ) + c * a ≤ a) :
    palScale r n h ^ (2 : ℕ) ≤ palScale r n a ∧
    palScale r n h ≤ r ^ (1 / (2 * L)) ∧
    palScale r n a / palScale r n h ≤ r ^ (c / L) ∧
    palScale r n a / palScale r n h ≤
      tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2) ∧
    tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2) ≤
      2 * r ^ (c / L) ∧
    palScale r n h ≤
      tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2) ∧
    4 * (16 * palScale r n h) * (palScale r n h / 2) ≤ 2 * (27 * palScale r n a) := by
  have hidx := caseA_window_indices hc hL hn hna hah hgap
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ := palScale_pos (n := n) hr h
  have hδ := palScale_pos (n := n) hr a
  have hsquare : palScale r n h ^ (2 : ℕ) ≤ palScale r n a := by
    rw [palScale_eq_rpow hr, palScale_eq_rpow hr, ← Real.rpow_natCast,
      ← Real.rpow_mul hr.le]
    apply Real.rpow_le_rpow_of_exponent_ge hr hr1.le
    exact (div_le_div_of_nonneg_right hah hnR.le).trans_eq (by ring)
  have hρsmall : palScale r n h ≤ r ^ (1 / (2 * L)) := by
    rw [palScale_eq_rpow hr]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1.le hidx.2.2.1
  have hratio : palScale r n a / palScale r n h ≤ r ^ (c / L) := by
    rw [palScale_eq_rpow hr, palScale_eq_rpow hr, ← Real.rpow_sub hr]
    apply Real.rpow_le_rpow_of_exponent_ge hr hr1.le
    simpa only [sub_div] using hidx.2.2.2
  have ht := tubeTol_half (δ := palScale r n a) hρ
  have htlow : palScale r n a / palScale r n h ≤
      tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2) := by
    rw [ht, div_le_div_iff₀ hρ (by positivity)]
    nlinarith only [hδ, hρ, sq_nonneg (palScale r n h)]
  have hthigh : tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2) ≤
      2 * (palScale r n a / palScale r n h) := by
    rw [ht, mul_div_assoc', div_le_div_iff₀ (by positivity) hρ]
    nlinarith only [hsquare, hδ, hρ]
  refine ⟨hsquare, hρsmall, hratio, htlow,
    hthigh.trans (mul_le_mul_of_nonneg_left hratio (by norm_num)), ?_, ?_⟩
  · rw [ht, le_div_iff₀ (by positivity)]
    nlinarith only [hsquare, hδ]
  · nlinarith only [hsquare, hδ]

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
