-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.StripNeighborhood.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Shear

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

lemma clamp_mem_unit (z : ℝ) : max (-1 : ℝ) (min 1 z) ∈ Icc (-1 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clamp_dist_le {z w : ℝ} (hw : w ∈ Icc (-1 : ℝ) 1) :
    |max (-1 : ℝ) (min 1 z) - w| ≤ |z - w| := by
  by_cases hz1 : z ≤ 1
  · rw [min_eq_right hz1]
    by_cases hzn : -1 ≤ z
    · rw [max_eq_right hzn]
    · rw [max_eq_left (le_of_not_ge hzn), abs_of_nonpos (by linarith [hw.1]),
        abs_of_nonpos (by linarith [hw.1])]
      linarith
  · rw [min_eq_left (le_of_not_ge hz1), max_eq_right (by norm_num),
      abs_of_nonneg (by linarith [hw.2]), abs_of_nonneg (by linarith [hw.2])]
    linarith

/-- A graph strip with a Lipschitz center has a linear bound for the area of its neighborhood. -/
theorem volume_thickening_graph_strip {g : ℝ → ℝ} (hg : Measurable g)
    {ρ r L B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : 0 ≤ r) (hrB : r ≤ B * ρ)
    (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hlip : ∀ z ∈ Icc (-1 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |g z - g w| ≤ L * |z - w|) :
    volume (thickening ρ {p : ℝ × ℝ | p.2 ∈ Icc (-1 : ℝ) 1 ∧ |p.1 - g p.2| ≤ r}) ≤
      ENNReal.ofReal (8 * (B + L + 1) * ρ) := by
  let a := r + (L + 1) * ρ
  let Φ := horizontalShear (h := fun z => -g (max (-1 : ℝ) (min 1 z))) (by fun_prop)
  let R := Icc (-a) a ×ˢ Icc (-1 - ρ) (1 + ρ)
  have hsub : thickening ρ {p : ℝ × ℝ | p.2 ∈ Icc (-1 : ℝ) 1 ∧ |p.1 - g p.2| ≤ r} ⊆
      Φ ⁻¹' R := by
    intro p hp
    obtain ⟨q, ⟨hqz, hqu⟩, hpq⟩ := mem_thickening_iff.mp hp
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hpq
    have hz : p.2 ∈ Icc (-1 - ρ) (1 + ρ) := by
      obtain ⟨h1, h2⟩ := abs_lt.mp hpq.2
      exact ⟨by linarith [hqz.1], by linarith [hqz.2]⟩
    have hclose : |g q.2 - g (max (-1 : ℝ) (min 1 p.2))| ≤ L * ρ := by
      calc
        _ = |g (max (-1 : ℝ) (min 1 p.2)) - g q.2| := abs_sub_comm _ _
        _ ≤ L * |max (-1 : ℝ) (min 1 p.2) - q.2| := hlip _ (clamp_mem_unit _) _ hqz
        _ ≤ L * |p.2 - q.2| := mul_le_mul_of_nonneg_left (clamp_dist_le hqz) hL
        _ ≤ L * ρ := mul_le_mul_of_nonneg_left hpq.2.le hL
    have hu : |p.1 - g (max (-1 : ℝ) (min 1 p.2))| ≤ a := by
      calc
        _ = |(p.1 - q.1) + (q.1 - g q.2) +
            (g q.2 - g (max (-1 : ℝ) (min 1 p.2)))| := by congr 1; ring
        _ ≤ |p.1 - q.1| + |q.1 - g q.2| +
            |g q.2 - g (max (-1 : ℝ) (min 1 p.2))| := abs_add_three _ _ _
        _ ≤ a := by dsimp [a]; linarith
    refine ⟨?_, hz⟩
    change -a ≤ p.1 + -g (max (-1 : ℝ) (min 1 p.2)) ∧
      p.1 + -g (max (-1 : ℝ) (min 1 p.2)) ≤ a
    simpa only [sub_eq_add_neg] using abs_le.mp hu
  have hRm : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have ha : 0 ≤ a := by dsimp [a]; positivity
  calc
    _ ≤ volume (Φ ⁻¹' R) := measure_mono hsub
    _ = volume R := (measurePreserving_horizontalShear _).measure_preimage hRm.nullMeasurableSet
    _ = ENNReal.ofReal (2 * a * (2 + 2 * ρ)) := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
        ← ENNReal.ofReal_mul (by linarith : 0 ≤ a - -a)]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h1 : a ≤ (B + L + 1) * ρ := by dsimp [a]; nlinarith
      have h2 : 2 + 2 * ρ ≤ 4 := by linarith
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)) h2
        (by positivity : 0 ≤ 2 + 2 * ρ) (by positivity : 0 ≤ 2 * ((B + L + 1) * ρ))
      nlinarith

lemma graph_center_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    (c : ℝ) (q : Space) {z w : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (hw : w ∈ Icc (-1 : ℝ) 1) :
    |(q 0 + c * z + q 1 * f z + q 2 * z * f z) -
      (q 0 + c * w + q 1 * f w + q 2 * w * f w)| ≤
        (|c| + 2 * |q 1| + 5 * |q 2|) * |z - w| := by
  have hfw := slope_lipschitz_on hf hderiv hz hw
  change |f z - f w| ≤ 2 * |z - w| at hfw
  have hfz := normalized_slope_bound hf hderiv hf0 hz
  have hw1 : |w| ≤ 1 := abs_le.mpr hw
  have hzf : |z * f z - w * f w| ≤ 5 * |z - w| := by
    calc
      _ = |(z - w) * f z + w * (f z - f w)| := by congr 1; ring
      _ ≤ |(z - w) * f z| + |w * (f z - f w)| := abs_add_le _ _
      _ = |z - w| * |f z| + |w| * |f z - f w| := by rw [abs_mul, abs_mul]
      _ ≤ |z - w| * 3 + 1 * (2 * |z - w|) := by gcongr
      _ = _ := by ring
  calc
    _ = |c * (z - w) + q 1 * (f z - f w) + q 2 * (z * f z - w * f w)| := by congr 1; ring
    _ ≤ |c * (z - w)| + |q 1 * (f z - f w)| + |q 2 * (z * f z - w * f w)| :=
      abs_add_three _ _ _
    _ = |c| * |z - w| + |q 1| * |f z - f w| + |q 2| * |z * f z - w * f w| := by
      rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |c| * |z - w| + |q 1| * (2 * |z - w|) + |q 2| * (5 * |z - w|) := by gcongr
    _ = _ := by ring

/-- A cinematic strip of width at most fifteen times the coarse scale has controlled area. -/
theorem volume_thickening_cinematic_strip {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    {ρ r c : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : 0 ≤ r) (hrρ : r ≤ 15 * ρ)
    (hc : |c| ≤ 3) (q : Space) (hq : ‖q‖ ≤ 5) :
    volume (thickening ρ (graphStrip r f c q)) ≤ ENNReal.ofReal (432 * ρ) := by
  have hb : |q 1| ≤ 5 := (abs_coordinate_le_norm q 1).trans hq
  have hd : |q 2| ≤ 5 := (abs_coordinate_le_norm q 2).trans hq
  have hL : |c| + 2 * |q 1| + 5 * |q 2| ≤ 38 := by linarith
  have hfm := hf.continuous.measurable
  have hh := volume_thickening_graph_strip
    (g := fun z => q 0 + c * z + q 1 * f z + q 2 * z * f z) (by fun_prop)
    hρ hρ1 hr hrρ (by norm_num : (0 : ℝ) ≤ 38) (by norm_num : (0 : ℝ) ≤ 15)
    (fun z hz w hw => (graph_center_lipschitz hf hderiv hf0 c q hz hw).trans
      (mul_le_mul_of_nonneg_right hL (abs_nonneg _)))
  norm_num at hh
  simpa only [graphStrip, mem_Icc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 432), ENNReal.ofReal_ofNat] using hh

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
