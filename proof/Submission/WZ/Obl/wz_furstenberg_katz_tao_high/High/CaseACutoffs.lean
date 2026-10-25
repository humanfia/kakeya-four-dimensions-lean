-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CaseACutoffs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseAScales
import Submission.WZ.Obl.wz_slab_local_linearity.SmallPowers

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

/-- The palette discretization costs half of the fixed tube-scale margin. -/
theorem caseA_base_times_scale {r c L : ℝ} {n h a : ℕ}
    (hr : 0 < r) (hr1 : r < 1) (hc : 0 < c) (hL : 1 ≤ L) (hn : 0 < n)
    (hnL : 4 * L ≤ (n : ℝ))
    (hna : (n : ℝ) ≤ L * a) (hah : (a : ℝ) ≤ 2 * h)
    (hgap : (h : ℝ) + c * a ≤ a) :
    palBase r n * palScale r n h ≤ r ^ (1 / (4 * L)) := by
  have hh := (caseA_window_indices hc hL hn hna hah hgap).2.2.1
  have hL0 : 0 < L := by linarith
  have hinv : 1 / (n : ℝ) ≤ 1 / (4 * L) :=
    one_div_le_one_div_of_le (by positivity) hnL
  rw [palBase, palScale_eq_rpow hr, ← Real.rpow_add hr]
  apply Real.rpow_le_rpow_of_exponent_ge hr hr1.le
  have he : 1 / (2 * L) = 2 * (1 / (4 * L)) := by field_simp; ring
  rw [he] at hh
  linarith only [hh, hinv]

/-- One palette step before the final scale is already at least `B r`. -/
theorem palScale_preterminal {r : ℝ} {n a : ℕ}
    (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n) (ha : a < n) :
    palBase r n * r ≤ palScale r n a := by
  have hB := palBase_gt_one hr hr1 hn
  have hB0 := palBase_pos (n := n) hr
  calc
    palBase r n * r = palBase r n ^ (1 : ℝ) * palBase r n ^ (-(n : ℝ)) := by
      rw [Real.rpow_one, palBase_pow_n hr hn]
    _ = palBase r n ^ (1 - (n : ℝ)) := by rw [← Real.rpow_add hB0]; congr 1
    _ ≤ palScale r n a := by
      apply Real.rpow_le_rpow_of_exponent_le hB.le
      have hh : (a : ℝ) + 1 ≤ n := by exact_mod_cast ha
      linarith

/-- Distinct palette indices are separated by a full factor of the base. -/
theorem palScale_ratio_le_inv {r : ℝ} {n h a : ℕ}
    (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n) (ha : h < a) :
    palScale r n a / palScale r n h ≤ (palBase r n)⁻¹ := by
  have hB := palBase_gt_one hr hr1 hn
  have hB0 := palBase_pos (n := n) hr
  unfold palScale
  rw [← Real.rpow_sub hB0, ← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le hB.le
  have hh : (h : ℝ) + 1 ≤ a := by exact_mod_cast ha
  linarith

/-- All geometric scale conditions of the selected-tube contradiction can
be imposed before seeing the configuration or the selected window. -/
theorem caseA_geometry_cutoff {c L δ₀ : ℝ}
    (hc : 0 < c) (hL : 1 ≤ L) (hδ₀ : 0 < δ₀) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 52 ∧
        ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ h a : ℕ, a < n →
          (n : ℝ) ≤ L * a → (a : ℝ) ≤ 2 * h → (h : ℝ) + c * a ≤ a →
          10 * r ≤ palScale r n a ∧
          30 * palScale r n a ≤ palScale r n h ∧
          palScale r n h ^ (2 : ℕ) ≤ palScale r n a ∧
          21440 * palBase r n * palScale r n h ≤ 1 / 2 ∧
          tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2) ≤ δ₀ ∧
          tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2) ≤
            2 * r ^ (c / L) := by
  have hL0 : 0 < L := by linarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (4 * L + 1)
  have hN₀pos : 0 < N₀ := by
    have : (0 : ℝ) < N₀ := by linarith
    exact_mod_cast this
  obtain ⟨rW, hrW, hwidth⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (a := 1 / (4 * L)) (B := 1 / 42880) (by positivity) (by norm_num)
  obtain ⟨rT, hrT, htolerance⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (a := c / L) (B := δ₀ / 2) (by positivity) (by positivity)
  refine ⟨N₀, hN₀pos, ?_⟩
  intro n hn
  have hnpos : 0 < n := hN₀pos.trans_le hn
  have hnL : 4 * L ≤ (n : ℝ) := by
    have hh : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨rB, hrB, _, hbase⟩ := exists_palBase_cutoff (A := 128) (by norm_num) hnpos
  refine ⟨min rB (min rW (min rT (1 / 52))),
    lt_min hrB (lt_min hrW (lt_min hrT (by norm_num))),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
  intro r hr hrr h a han hna hah hgap
  have hrB' := hrr.trans (min_le_left _ _)
  have hrW' := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrT' := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr52 : r ≤ 1 / 52 := hrr.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr1 : r < 1 := by linarith
  have hB := hbase r hr hrB'
  have hidx := caseA_window_indices hc hL hnpos hna hah hgap
  have hsc := caseA_window_scales hr hr1 hc hL hnpos hna hah hgap
  have hρ := palScale_pos (n := n) hr h
  have hδ := palScale_pos (n := n) hr a
  have hB0 := palBase_pos (n := n) hr
  have h10 : 10 * r ≤ palScale r n a := by
    refine le_trans ?_ (palScale_preterminal hr hr1 hnpos han)
    exact mul_le_mul_of_nonneg_right (by linarith) hr.le
  have h30 : 30 * palScale r n a ≤ palScale r n h := by
    have hh := palScale_ratio_le_inv hr hr1 hnpos hidx.2.1
    have hratio : palScale r n a / palScale r n h ≤ 1 / 30 :=
      hh.trans (by simpa only [one_div] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 30) (by linarith : 30 ≤ palBase r n))
    have hm := (div_le_iff₀ hρ).mp hratio
    linarith
  have hwidth' := (caseA_base_times_scale hr hr1 hc hL hnpos hnL hna hah hgap).trans
    (hwidth r hr hrW')
  have htol' := htolerance r hr hrT'
  refine ⟨h10, h30, hsc.1, ?_, ?_, hsc.2.2.2.2.1⟩
  · nlinarith only [hwidth']
  · have hh := hsc.2.2.2.2.1
    linarith only [hh, htol']

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
