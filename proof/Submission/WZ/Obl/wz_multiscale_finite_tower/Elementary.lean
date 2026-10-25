-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Elementary.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Local

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

lemma FrameAdmissible.union_ne_top {d r θ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : FrameAdmissible d r θ n x v Y) :
    volume (⋃ i, Y i) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (measure_ball_ne_top (μ := volume) (x := (0 : Space)) (r := 1))
  exact measure_mono (Set.iUnion_subset fun i => (h.2.1 i).2.2.2.trans (h.2.1 i).2.1)

/-- Averaging the shading mass always gives a lower bound for the union. -/
lemma FrameAdmissible.union_lower {d r θ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : FrameAdmissible d r θ n x v Y) (hd : 0 < d) :
    ENNReal.ofReal (d ^ θ * r ^ 2) ≤ volume (⋃ i, Y i) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr h.1
  have hs : (∑ i, volume (Y i)) ≤ (n : ℝ≥0∞) * volume (⋃ i, Y i) := by
    calc
      _ ≤ ∑ _i : Fin n, volume (⋃ i, Y i) := Finset.sum_le_sum (fun i _ =>
        measure_mono (Set.subset_iUnion Y i))
      _ = _ := by simp [nsmul_eq_mul]
  have hv := h.2.2.2.1.trans hs
  rw [← ENNReal.ofReal_toReal h.union_ne_top, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul hn.le] at hv
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hv
  apply (ENNReal.ofReal_le_iff_le_toReal h.union_ne_top).mpr
  nlinarith

/-- The input convex count bounds the total number of tubes inside the unit ball. -/
lemma FrameAdmissible.card_bound {d r θ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : FrameAdmissible d r θ n x v Y) (hd : 0 < d) :
    (n : ℝ) * r ^ 2 ≤ 16 * d ^ (-θ) := by
  have hball : volume (Metric.ball (0 : Space) 1) ≤ ENNReal.ofReal 16 := by
    rw [EuclideanSpace.volume_ball_fin_three]
    norm_num
    linarith [Real.pi_lt_four]
  have hcount := h.2.2.2.2.1 (Metric.ball 0 1) (convex_ball _ _)
  have hset : {i | Tube r (x i) (v i) ⊆ Metric.ball 0 1} = Set.univ :=
    Set.eq_univ_iff_forall.mpr (fun i => (h.2.1 i).2.1)
  rw [hset, Set.ncard_univ, Nat.card_fin] at hcount
  have hb := hcount.trans (mul_le_mul_of_nonneg_left hball (by positivity))
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)] at hb
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  simpa only [mul_comm] using hr

/-- At a small logarithmic gap, elementary density pays for the complete volume factor. -/
theorem FrameAdmissible.small_gap {σ ω d r θ h loss : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hA : FrameAdmissible d r θ n x v Y)
    (hd : 0 < d) (hd1 : d ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 ≤ ω)
    (hgap : d ^ h ≤ r) (hbudget : 2 * θ + (5 / 2 : ℝ) * h ≤ loss) :
    ENNReal.ofReal ((1 / 16 : ℝ) * d ^ loss * volumeFactor σ ω r n) ≤ volume (⋃ i, Y i) := by
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hA.1
  have hnr : r ≤ (n : ℝ) * r := by nlinarith
  have hcard := hA.card_bound hd
  have hpow : (n * r) ^ (-σ) ≤ d ^ (-h / 2) := by
    calc
      (n * r) ^ (-σ) ≤ r ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hr hnr (neg_nonpos.mpr hσ)
      _ ≤ r ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
      _ ≤ (d ^ h) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hd _) hgap (by norm_num)
      _ = d ^ (-h / 2) := by rw [← Real.rpow_mul hd.le]; congr 1; ring
  have hfac : volumeFactor σ ω r n ≤ 16 * d ^ (-θ - h / 2) := by
    calc
      volumeFactor σ ω r n ≤ 1 * (16 * d ^ (-θ)) * d ^ (-h / 2) := by
        dsimp [volumeFactor]
        apply mul_le_mul
        · exact mul_le_mul (Real.rpow_le_one hr.le hr1 hω) hcard (by positivity) zero_le_one
        · exact hpow
        · positivity
        · positivity
      _ = _ := by rw [one_mul, mul_assoc, ← Real.rpow_add hd]; congr 2; ring
  have hrpow : d ^ (2 * h) ≤ r ^ 2 := by
    rw [show (2 : ℝ) * h = h * (2 : ℝ) by ring, Real.rpow_mul hd.le, Real.rpow_two]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hd.le _) hgap 2
  apply le_trans (ENNReal.ofReal_le_ofReal _) (hA.union_lower hd)
  calc
    (1 / 16 : ℝ) * d ^ loss * volumeFactor σ ω r n ≤
        (1 / 16 : ℝ) * d ^ loss * (16 * d ^ (-θ - h / 2)) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = d ^ (loss - θ - h / 2) := by
      calc
        _ = d ^ loss * d ^ (-θ - h / 2) := by ring
        _ = _ := by rw [← Real.rpow_add hd]; congr 1; ring
    _ ≤ d ^ (θ + 2 * h) := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
    _ = d ^ θ * d ^ (2 * h) := Real.rpow_add hd _ _
    _ ≤ d ^ θ * r ^ 2 := mul_le_mul_of_nonneg_left hrpow (by positivity)

end WangZahlLot.Obl.wz_multiscale_finite_tower
