-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tube_packing_bound.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_tube_packing_bound`

At most `C δ⁻⁴` essentially distinct `δ`-tubes around unit segments fit in the unit ball.

* `homothety_image_subset`: if `y = x + s v + q` with `|s| ≤ 1/20`, `‖q‖ ≤ δ/20` and
  `‖v - w‖ ≤ δ/20`, the homothety of ratio `9/10` about `x + (10 s + 1/2) v` maps the tube
  around `[x, x + v]` into both tubes;
* `not_close`: its image has `(9/10)³ > 1/2` of the tube's volume, so two tubes of the family
  are never that close;
* `cell`: a tube is labelled by a coordinate `k` with `|v k| ≥ 1/2` (its chart), the sign of
  `v k`, its axial parameter `t = x k / v k` to precision `1/20`, and the two other coordinates
  of `v` and of the trace `x - t v` (on the plane `{p k = 0}`) to precision `ε = δ/240`;
* `close_of_cell_eq`: tubes with the same label are close in the above sense, so the label is
  injective on the family and there are at most `480 ⌈6/ε⌉₊⁴ ≤ 480 · 1441⁴ δ⁻⁴` tubes.
-/

namespace WangZahlLot.Obl.wz_tube_packing_bound

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- The homothety of ratio `9/10` about `x + (10 s + 1/2) v` maps the tube around `[x, x + v]`
into both tubes when `y = x + s v + q`, `|s| ≤ 1/20`, `‖q‖ ≤ δ/20` and `‖v - w‖ ≤ δ/20`. -/
theorem homothety_image_subset {δ s : ℝ} {x v y w q : Space}
    (hs : |s| ≤ 1 / 20) (hvw : ‖v - w‖ ≤ δ / 20) (hq : ‖q‖ ≤ δ / 20)
    (hy : y = x + s • v + q) :
    AffineMap.homothety (x + (10 * s + 1 / 2) • v) (9 / 10 : ℝ) ''
        thickening δ (segment ℝ x (x + v)) ⊆
      thickening δ (segment ℝ x (x + v)) ∩ thickening δ (segment ℝ y (y + w)) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨a, ha, hpa⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at ha
  obtain ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩ := ha
  obtain ⟨hs0, hs1⟩ := abs_le.mp hs
  set h := AffineMap.homothety (x + (10 * s + 1 / 2) • v) (9 / 10 : ℝ) with hh
  have hha : h (x + τ • (x + v - x)) = x + ((9 / 10) * τ + s + 1 / 20) • v := by
    rw [hh, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  have hdist : dist (h p) (h (x + τ • (x + v - x))) < 9 / 10 * δ := by
    rw [hh, dist_homothety, Real.norm_of_nonneg (by norm_num)]
    linarith
  have hb : dist (x + ((9 / 10) * τ + s + 1 / 20) • v) (y + ((9 / 10) * τ + 1 / 20) • w)
      ≤ δ / 10 := by
    rw [dist_eq_norm, hy]
    have e : x + ((9 / 10) * τ + s + 1 / 20) • v - (x + s • v + q + ((9 / 10) * τ + 1 / 20) • w)
        = ((9 / 10) * τ + 1 / 20) • (v - w) - q := by module
    rw [e]
    have hc : |(9 / 10) * τ + 1 / 20| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc ‖((9 / 10) * τ + 1 / 20) • (v - w) - q‖
        ≤ ‖((9 / 10) * τ + 1 / 20) • (v - w)‖ + ‖q‖ := norm_sub_le _ _
      _ = |(9 / 10) * τ + 1 / 20| * ‖v - w‖ + ‖q‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (δ / 20) + δ / 20 := by gcongr
      _ = δ / 10 := by ring
  refine ⟨mem_thickening_iff.mpr ⟨x + ((9 / 10) * τ + s + 1 / 20) • v, ?_, ?_⟩,
    mem_thickening_iff.mpr ⟨y + ((9 / 10) * τ + 1 / 20) • w, ?_, ?_⟩⟩
  · rw [segment_eq_image']
    exact ⟨(9 / 10) * τ + s + 1 / 20, ⟨by linarith, by linarith⟩, by simp⟩
  · rw [← hha]
    have hδ : 0 ≤ δ := by linarith [dist_nonneg (x := p) (y := x + τ • (x + v - x))]
    linarith
  · rw [segment_eq_image']
    exact ⟨(9 / 10) * τ + 1 / 20, ⟨by linarith, by linarith⟩, by simp⟩
  · calc dist (h p) (y + ((9 / 10) * τ + 1 / 20) • w)
        ≤ dist (h p) (h (x + τ • (x + v - x)))
          + dist (h (x + τ • (x + v - x))) (y + ((9 / 10) * τ + 1 / 20) • w) :=
          dist_triangle _ _ _
      _ < 9 / 10 * δ + δ / 10 := by rw [hha] at hdist ⊢; linarith
      _ = δ := by ring

/-- A tube has positive volume. -/
theorem tube_volume_pos {δ : ℝ} (hδ : 0 < δ) (x v : Space) :
    0 < volume (thickening δ (segment ℝ x (x + v))) :=
  isOpen_thickening.measure_pos _
    ⟨x, self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))⟩

/-- Two tubes of a family with the half-overlap condition are never close. -/
theorem not_close {δ s : ℝ} {x v y w q : Space} (hδ : 0 < δ)
    (hB : thickening δ (segment ℝ x (x + v)) ⊆ ball (0 : Space) 1)
    (hover : volume (thickening δ (segment ℝ x (x + v)) ∩ thickening δ (segment ℝ y (y + w)))
      ≤ (1 / 2 : ℝ≥0∞) * volume (thickening δ (segment ℝ x (x + v))))
    (hs : |s| ≤ 1 / 20) (hvw : ‖v - w‖ ≤ δ / 20) (hq : ‖q‖ ≤ δ / 20)
    (hy : y = x + s • v + q) : False := by
  set T := thickening δ (segment ℝ x (x + v)) with hT
  have hpos : volume T ≠ 0 := (tube_volume_pos hδ x v).ne'
  have hfin : volume T ≠ ∞ := ((measure_mono hB).trans_lt measure_ball_lt_top).ne
  have h1 : ENNReal.ofReal ((9 / 10 : ℝ) ^ 3) * volume T
      ≤ volume (T ∩ thickening δ (segment ℝ y (y + w))) := by
    calc ENNReal.ofReal ((9 / 10 : ℝ) ^ 3) * volume T
        = volume (AffineMap.homothety (x + (10 * s + 1 / 2) • v) (9 / 10 : ℝ) '' T) := by
          rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
          congr 2
          rw [abs_of_pos (by norm_num)]
      _ ≤ _ := measure_mono (homothety_image_subset hs hvw hq hy)
  have h2 := (ENNReal.mul_le_mul_iff_left hpos hfin).mp (h1.trans hover)
  have h3 : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h3, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h2
  norm_num at h2

/-- `‖u‖²` as the sum of the squares of the coordinates `k`, `k + 1`, `k + 2`. -/
theorem norm_sq_eq_three (u : Space) (k : Fin 3) :
    ‖u‖ ^ 2 = u k ^ 2 + u (k + 1) ^ 2 + u (k + 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  fin_cases k <;> simp <;> ring

theorem abs_apply_le_norm (u : Space) (k : Fin 3) : |u k| ≤ ‖u‖ := by
  rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le u k

/-- The chart of a unit vector: a coordinate where it is at least `1/2` in absolute value. -/
noncomputable def chart (v : Space) : Fin 3 :=
  if 1 / 2 ≤ |v 0| then 0 else if 1 / 2 ≤ |v 1| then 1 else 2

theorem half_le_abs_chart {v : Space} (hv : ‖v‖ = 1) : 1 / 2 ≤ |v (chart v)| := by
  have h := norm_sq_eq_three v 0
  rw [hv] at h
  have h' : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by simpa using h.symm
  by_cases h0 : 1 / 2 ≤ |v 0|
  · rw [chart, ite_eq_left h0]; exact h0
  by_cases h1 : 1 / 2 ≤ |v 1|
  · rw [chart, ite_eq_right h0, ite_eq_left h1]; exact h1
  rw [chart, ite_eq_right h0, ite_eq_right h1]
  by_contra h2
  rw [not_le] at h0 h1 h2
  have s0 : |v 0| ^ 2 < (1 / 2) ^ 2 := pow_lt_pow_left₀ h0 (abs_nonneg _) two_ne_zero
  have s1 : |v 1| ^ 2 < (1 / 2) ^ 2 := pow_lt_pow_left₀ h1 (abs_nonneg _) two_ne_zero
  have s2 : |v 2| ^ 2 < (1 / 2) ^ 2 := pow_lt_pow_left₀ h2 (abs_nonneg _) two_ne_zero
  rw [sq_abs] at s0 s1 s2
  norm_num at s0 s1 s2
  linarith

/-- The axial parameter `t = x k / v k` of the line `x + ℝ v` in its chart `k`. -/
noncomputable def axial (x v : Space) : ℝ := x (chart v) / v (chart v)

/-- The trace `x - t v` of the line `x + ℝ v` on the plane `{p k = 0}` of its chart `k`. -/
noncomputable def trace (x v : Space) : Space := x - axial x v • v

/-- The label of a tube: chart, sign, axial parameter, two coordinates of the direction and two
of the trace, each rounded. -/
noncomputable def cell (ε : ℝ) (x v : Space) : Fin 3 × Bool × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (chart v, decide (0 < v (chart v)), ⌊(axial x v + 2) / (1 / 20)⌋₊,
    ⌊(v (chart v + 1) + 3) / ε⌋₊, ⌊(v (chart v + 2) + 3) / ε⌋₊,
    ⌊(trace x v (chart v + 1) + 3) / ε⌋₊, ⌊(trace x v (chart v + 2) + 3) / ε⌋₊)

theorem abs_axial_lt {x v : Space} (hv : ‖v‖ = 1) (hx : ‖x‖ < 1) : |axial x v| < 2 := by
  have h1 := half_le_abs_chart hv
  have h2 := (abs_apply_le_norm x (chart v)).trans_lt hx
  unfold axial
  rw [abs_div, div_lt_iff₀ (by linarith)]
  linarith

theorem trace_apply_chart (x v : Space) (hv : ‖v‖ = 1) : trace x v (chart v) = 0 := by
  have h1 := half_le_abs_chart hv
  have hne : v (chart v) ≠ 0 := by
    intro h; rw [h, abs_zero] at h1; norm_num at h1
  simp only [trace, axial, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem abs_trace_apply_lt {x v : Space} (hv : ‖v‖ = 1) (hx : ‖x‖ < 1) (m : Fin 3) :
    |trace x v m| < 3 := by
  have h1 := abs_axial_lt hv hx
  have h2 := (abs_apply_le_norm x m).trans_lt hx
  have h3 := (abs_apply_le_norm v m).trans_eq hv
  simp only [trace, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  calc |x m - axial x v * v m| ≤ |x m| + |axial x v| * |v m| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ < 1 + 2 * 1 := by
        have := mul_le_mul h1.le h3 (abs_nonneg _) (by norm_num)
        linarith
    _ = 3 := by norm_num

theorem abs_sub_lt_of_floor_eq {a b ε : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ⌊a / ε⌋₊ = ⌊b / ε⌋₊) : |a - b| < ε := by
  have h1 := Nat.floor_le (div_nonneg ha hε.le)
  have h2 := Nat.lt_floor_add_one (a / ε)
  have h3 := Nat.floor_le (div_nonneg hb hε.le)
  have h4 := Nat.lt_floor_add_one (b / ε)
  rw [h] at h1 h2
  have h5 : |a / ε - b / ε| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  rwa [← sub_div, abs_div, abs_of_pos hε, div_lt_one hε] at h5

theorem floor_lt_ceil {a ε c : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hac : a < c) :
    ⌊a / ε⌋₊ < ⌈c / ε⌉₊ :=
  (Nat.floor_lt (div_nonneg ha hε.le)).mpr
    ((div_lt_div_of_pos_right hac hε).trans_le (Nat.le_ceil _))

/-- Every label lies in a box with `480 ⌈6/ε⌉₊⁴` elements. -/
theorem cell_mem {ε : ℝ} (hε : 0 < ε) {x v : Space} (hv : ‖v‖ = 1) (hx : ‖x‖ < 1) :
    cell ε x v ∈ (Finset.univ ×ˢ Finset.univ ×ˢ Finset.range ⌈4 / (1 / 20 : ℝ)⌉₊ ×ˢ
      Finset.range ⌈6 / ε⌉₊ ×ˢ Finset.range ⌈6 / ε⌉₊ ×ˢ Finset.range ⌈6 / ε⌉₊ ×ˢ
      Finset.range ⌈6 / ε⌉₊ : Finset (Fin 3 × Bool × ℕ × ℕ × ℕ × ℕ × ℕ)) := by
  have ht := abs_lt.mp (abs_axial_lt hv hx)
  have hv1 := abs_le.mp ((abs_apply_le_norm v (chart v + 1)).trans_eq hv)
  have hv2 := abs_le.mp ((abs_apply_le_norm v (chart v + 2)).trans_eq hv)
  have hp1 := abs_lt.mp (abs_trace_apply_lt hv hx (chart v + 1))
  have hp2 := abs_lt.mp (abs_trace_apply_lt hv hx (chart v + 2))
  simp only [cell, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
  refine ⟨floor_lt_ceil (by norm_num) ?_ ?_, floor_lt_ceil hε ?_ ?_, floor_lt_ceil hε ?_ ?_,
    floor_lt_ceil hε ?_ ?_, floor_lt_ceil hε ?_ ?_⟩ <;> linarith

/-- Two unit vectors in the same chart with the same sign and close off-chart coordinates are
close. -/
theorem norm_sub_le_of_coords {ε : ℝ} (hε : 0 < ε) {v w : Space} (k : Fin 3)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvk : 1 / 2 ≤ |v k|) (hwk : 1 / 2 ≤ |w k|)
    (hsign : 0 < v k ↔ 0 < w k) (h1 : |v (k + 1) - w (k + 1)| < ε)
    (h2 : |v (k + 2) - w (k + 2)| < ε) : ‖v - w‖ ≤ 5 * ε := by
  have nv := norm_sq_eq_three v k
  have nw := norm_sq_eq_three w k
  have nvw := norm_sq_eq_three (v - w) k
  simp only [PiLp.sub_apply] at nvw
  rw [hv] at nv
  rw [hw] at nw
  have b1 := abs_le.mp ((abs_apply_le_norm v (k + 1)).trans_eq hv)
  have b2 := abs_le.mp ((abs_apply_le_norm v (k + 2)).trans_eq hv)
  have c1 := abs_le.mp ((abs_apply_le_norm w (k + 1)).trans_eq hw)
  have c2 := abs_le.mp ((abs_apply_le_norm w (k + 2)).trans_eq hw)
  -- `|v k + w k| ≥ 1`
  have hsum : 1 ≤ |v k + w k| := by
    by_cases hp : 0 < v k
    · have hq := hsign.mp hp
      rw [abs_of_pos hp] at hvk
      rw [abs_of_pos hq] at hwk
      rw [abs_of_pos (by linarith)]; linarith
    · have hq : ¬ 0 < w k := fun h => hp (hsign.mpr h)
      rw [not_lt] at hp hq
      rw [abs_of_nonpos hp] at hvk
      rw [abs_of_nonpos hq] at hwk
      rw [abs_of_neg (by linarith)]; linarith
  have f1 : |(w (k + 1) - v (k + 1)) * (w (k + 1) + v (k + 1))| ≤ ε * 2 := by
    rw [abs_mul]
    apply mul_le_mul _ _ (abs_nonneg _) hε.le
    · rw [abs_sub_comm]; exact h1.le
    · rw [abs_le]; constructor <;> linarith
  have f2 : |(w (k + 2) - v (k + 2)) * (w (k + 2) + v (k + 2))| ≤ ε * 2 := by
    rw [abs_mul]
    apply mul_le_mul _ _ (abs_nonneg _) hε.le
    · rw [abs_sub_comm]; exact h2.le
    · rw [abs_le]; constructor <;> linarith
  -- `|v k - w k| |v k + w k| = |v k ^ 2 - w k ^ 2| ≤ 4 ε`
  have hdiff : |v k - w k| * |v k + w k| ≤ 4 * ε := by
    rw [← abs_mul]
    have e : (v k - w k) * (v k + w k) = (w (k + 1) - v (k + 1)) * (w (k + 1) + v (k + 1))
        + (w (k + 2) - v (k + 2)) * (w (k + 2) + v (k + 2)) := by linear_combination nw - nv
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ ε * 2 + ε * 2 := add_le_add f1 f2
      _ = 4 * ε := by ring
  have hk : |v k - w k| ≤ 4 * ε :=
    calc |v k - w k| = |v k - w k| * 1 := (mul_one _).symm
      _ ≤ |v k - w k| * |v k + w k| := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ ≤ 4 * ε := hdiff
  have g0 : (v k - w k) ^ 2 ≤ (4 * ε) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hk 2
  have g1 : (v (k + 1) - w (k + 1)) ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1.le 2
  have g2 : (v (k + 2) - w (k + 2)) ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2.le 2
  have hn : ‖v - w‖ ^ 2 ≤ (5 * ε) ^ 2 := by
    rw [nvw]
    have : (4 * ε) ^ 2 + ε ^ 2 + ε ^ 2 ≤ (5 * ε) ^ 2 := by
      have := sq_nonneg ε; ring_nf; linarith
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hn

/-- Tubes with the same label are close. -/
theorem close_of_cell_eq {ε : ℝ} (hε : 0 < ε) {x v y w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (h : cell ε x v = cell ε y w) :
    ‖v - w‖ ≤ 5 * ε ∧ ∃ s : ℝ, ∃ q : Space, |s| ≤ 1 / 20 ∧ ‖q‖ ≤ 12 * ε ∧
      y = x + s • v + q := by
  simp only [cell, Prod.mk.injEq] at h
  obtain ⟨hk, hσ, ht, hv1, hv2, hp1, hp2⟩ := h
  have hvk := half_le_abs_chart hv
  have hwk := half_le_abs_chart hw
  rw [← hk] at hwk hv1 hv2 hσ hp1 hp2
  have hx0 : trace x v (chart v) = 0 := trace_apply_chart x v hv
  have hy0 : trace y w (chart v) = 0 := by rw [hk]; exact trace_apply_chart y w hw
  set k := chart v with hkdef
  have hsign : 0 < v k ↔ 0 < w k := by simpa using hσ
  -- bounds
  have bv1 := abs_le.mp ((abs_apply_le_norm v (k + 1)).trans_eq hv)
  have bv2 := abs_le.mp ((abs_apply_le_norm v (k + 2)).trans_eq hv)
  have bw1 := abs_le.mp ((abs_apply_le_norm w (k + 1)).trans_eq hw)
  have bw2 := abs_le.mp ((abs_apply_le_norm w (k + 2)).trans_eq hw)
  have tx := abs_lt.mp (abs_axial_lt hv hx)
  have ty := abs_lt.mp (abs_axial_lt hw hy)
  have px1 := abs_lt.mp (abs_trace_apply_lt hv hx (k + 1))
  have px2 := abs_lt.mp (abs_trace_apply_lt hv hx (k + 2))
  have py1 := abs_lt.mp (abs_trace_apply_lt hw hy (k + 1))
  have py2 := abs_lt.mp (abs_trace_apply_lt hw hy (k + 2))
  have e1 := abs_sub_lt_of_floor_eq hε (by linarith) (by linarith) hv1
  have e2 := abs_sub_lt_of_floor_eq hε (by linarith) (by linarith) hv2
  have e3 := abs_sub_lt_of_floor_eq hε (by linarith) (by linarith) hp1
  have e4 := abs_sub_lt_of_floor_eq hε (by linarith) (by linarith) hp2
  have e5 := abs_sub_lt_of_floor_eq (by norm_num) (by linarith) (by linarith) ht
  simp only [add_sub_add_right_eq_sub] at e1 e2 e3 e4 e5
  have hvw := norm_sub_le_of_coords hε k hv hw hvk hwk hsign e1 e2
  refine ⟨hvw, axial y w - axial x v, (trace y w - trace x v) + axial y w • (w - v),
    ?_, ?_, ?_⟩
  · rw [abs_sub_comm]; exact e5.le
  · -- the traces differ by at most `2 ε`
    have hpk : trace y w k - trace x v k = 0 := by rw [hx0, hy0]; ring
    have hp : ‖trace y w - trace x v‖ ≤ 2 * ε := by
      have n := norm_sq_eq_three (trace y w - trace x v) k
      simp only [PiLp.sub_apply] at n
      rw [hpk] at n
      have f1 : (trace y w (k + 1) - trace x v (k + 1)) ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs, abs_sub_comm]; exact pow_le_pow_left₀ (abs_nonneg _) e3.le 2
      have f2 : (trace y w (k + 2) - trace x v (k + 2)) ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs, abs_sub_comm]; exact pow_le_pow_left₀ (abs_nonneg _) e4.le 2
      have : ‖trace y w - trace x v‖ ^ 2 ≤ (2 * ε) ^ 2 := by
        rw [n]
        have : (0 : ℝ) ^ 2 + ε ^ 2 + ε ^ 2 ≤ (2 * ε) ^ 2 := by
          have := sq_nonneg ε; ring_nf; linarith
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
    have hwv : ‖w - v‖ ≤ 5 * ε := by rw [norm_sub_rev]; exact hvw
    have hty : |axial y w| ≤ 2 := (abs_axial_lt hw hy).le
    calc ‖(trace y w - trace x v) + axial y w • (w - v)‖
        ≤ ‖trace y w - trace x v‖ + ‖axial y w • (w - v)‖ := norm_add_le _ _
      _ = ‖trace y w - trace x v‖ + |axial y w| * ‖w - v‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 2 * ε + 2 * (5 * ε) := by gcongr
      _ = 12 * ε := by ring
  · simp only [trace]
    module

end WangZahlLot.Obl.wz_tube_packing_bound

open WangZahlLot.Obl.wz_tube_packing_bound in
theorem WangZahlLot.wz_tube_packing_bound : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space), (∀ i, ‖v i‖ = 1) → (∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1/2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (n : ℝ) * δ ^ 4 ≤ C := by
  refine ⟨480 * 1441 ^ 4, by positivity, ?_⟩
  intro δ hδ hδ1 n x v hv hB hover
  set ε := δ / 240 with hε_def
  have hε : 0 < ε := by positivity
  have hx : ∀ i, ‖x i‖ < 1 := fun i => by
    have := hB i (Metric.self_subset_thickening hδ _ (left_mem_segment ℝ (x i) (x i + v i)))
    simpa using this
  have hmaps : Set.MapsTo (fun i => cell ε (x i) (v i)) (Finset.univ : Finset (Fin n))
      (Finset.univ ×ˢ Finset.univ ×ˢ Finset.range ⌈4 / (1 / 20 : ℝ)⌉₊ ×ˢ
      Finset.range ⌈6 / ε⌉₊ ×ˢ Finset.range ⌈6 / ε⌉₊ ×ˢ Finset.range ⌈6 / ε⌉₊ ×ˢ
      Finset.range ⌈6 / ε⌉₊ : Finset (Fin 3 × Bool × ℕ × ℕ × ℕ × ℕ × ℕ)) :=
    fun i _ => cell_mem hε (hv i) (hx i)
  have hinj : Set.InjOn (fun i => cell ε (x i) (v i)) (Finset.univ : Finset (Fin n)) := by
    intro i _ j _ hij
    by_contra hne
    obtain ⟨hvw, s, q, hs, hq, hy⟩ := close_of_cell_eq hε (hv i) (hv j) (hx i) (hx j) hij
    exact not_close hδ (hB i) (hover i j hne) hs (by linarith) (by linarith) hy
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have h80 : ⌈4 / (1 / 20 : ℝ)⌉₊ = 80 := by norm_num
  rw [h80] at hcard
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_product, Fintype.card_bool,
    Finset.card_range] at hcard
  have hM : (⌈6 / ε⌉₊ : ℝ) ≤ 1441 / δ := by
    have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 6 / ε by positivity)
    have h2 : 6 / ε = 1440 / δ := by rw [hε_def]; field_simp; norm_num
    have h3 : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have h4 : 1441 / δ = 1440 / δ + 1 / δ := by ring
    linarith
  have hn : (n : ℝ) ≤ 480 * (⌈6 / ε⌉₊ : ℝ) ^ 4 := by
    have : (n : ℝ) ≤ ((3 * (2 * (80 * (⌈6 / ε⌉₊ * (⌈6 / ε⌉₊ * (⌈6 / ε⌉₊ * ⌈6 / ε⌉₊))))) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    push_cast at this
    linarith
  calc (n : ℝ) * δ ^ 4 ≤ 480 * (⌈6 / ε⌉₊ : ℝ) ^ 4 * δ ^ 4 := by gcongr
    _ ≤ 480 * (1441 / δ) ^ 4 * δ ^ 4 := by gcongr
    _ = 480 * 1441 ^ 4 := by field_simp
