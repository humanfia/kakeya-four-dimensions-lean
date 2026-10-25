-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.LensGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.CurvatureOrder

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set

/-- The second-order lower Taylor bound, with the lower curvature bound
needed only between the two evaluation times. -/
theorem quadratic_gap_of_curvature {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {x y c : ℝ}
    (hc : ∀ t ∈ uIcc x y, c ≤ deriv (deriv f) t) :
    f x + deriv f x * (y - x) + c / 2 * (y - x) ^ 2 ≤ f y := by
  by_cases hxy : x = y
  · subst y
    simp
  obtain ⟨t, ht, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1)
    hxy hf.contDiffOn
  have hd := (hf.differentiable (by norm_num)) x
  have huniq : UniqueDiffWithinAt ℝ (uIcc x y) x :=
    (uniqueDiffOn_uIcc hxy) _ left_mem_uIcc
  rw [taylorWithinEval_succ f 0] at he
  simp only [taylor_within_zero_eval, Nat.cast_zero, zero_add, Nat.factorial_zero,
    Nat.cast_one, mul_one, inv_one, one_mul, pow_one, iteratedDerivWithin_one,
    smul_eq_mul, hd.derivWithin huniq] at he
  have hh := hc t (Ioo_subset_Icc_self ht)
  simp only [Nat.reduceAdd, Nat.factorial_succ, Nat.factorial_zero,
    Nat.cast_ofNat, mul_one, iteratedDeriv_succ, iteratedDeriv_zero] at he
  have hp := mul_le_mul_of_nonneg_right hh (sq_nonneg (y - x))
  nlinarith

/-- An approximate contact with a positively curved difference gives a
quadratic lower gap away from the contact time. -/
theorem contact_quadratic_gap {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {x y c δ η : ℝ}
    (hc : ∀ t ∈ uIcc x y, c ≤ deriv (deriv f) t)
    (hvalue : |f x| ≤ δ) (hslope : |deriv f x| ≤ η) :
    c / 2 * |y - x| ^ 2 - η * |y - x| - δ ≤ f y := by
  have h := quadratic_gap_of_curvature hf hc
  have hprod : -(η * |y - x|) ≤ deriv f x * (y - x) := by
    have hm := mul_le_mul_of_nonneg_right hslope (abs_nonneg (y - x))
    have ha := neg_abs_le (deriv f x * (y - x))
    rw [abs_mul] at ha
    linarith
  rw [sq_abs]
  linarith [(abs_le.mp hvalue).1]

/-- A level only twice the value error can be reached only within the sum
of the slope-error scale and the natural square-root scale. -/
theorem contact_sublevel_radius {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {x y c δ η : ℝ}
    (hc : 0 < c) (hcurv : ∀ t ∈ uIcc x y, c ≤ deriv (deriv f) t)
    (hvalue : |f x| ≤ δ) (hslope : |deriv f x| ≤ η) (hy : f y ≤ 2 * δ) :
    |y - x| ≤ max (4 * η / c) (4 * Real.sqrt (δ / c)) := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hvalue
  have hη : 0 ≤ η := (abs_nonneg _).trans hslope
  have hgap := contact_quadratic_gap hf hcurv hvalue hslope
  by_contra hn
  have hL : max (4 * η / c) (4 * Real.sqrt (δ / c)) < |y - x| := lt_of_not_ge hn
  have hLη := (le_max_left (4 * η / c) (4 * Real.sqrt (δ / c))).trans_lt hL
  have hLδ := (le_max_right (4 * η / c) (4 * Real.sqrt (δ / c))).trans_lt hL
  have hL0 : 0 < |y - x| := (by positivity : 0 ≤ 4 * Real.sqrt (δ / c)).trans_lt hLδ
  have hηmul := mul_lt_mul_of_pos_right ((div_lt_iff₀ hc).mp hLη) hL0
  have hroot := Real.sq_sqrt (div_nonneg hδ hc.le)
  have hrootmul : (Real.sqrt (δ / c)) ^ 2 * c = δ := (eq_div_iff hc.ne').mp hroot
  have hsquare : 16 * (Real.sqrt (δ / c)) ^ 2 < |y - x| ^ 2 := by
    nlinarith [Real.sqrt_nonneg (δ / c)]
  have hδmul := mul_lt_mul_of_pos_right hsquare hc
  nlinarith

/-- A contact with enough room on both sides produces a genuine lens after
raising the comparison level to twice the value tolerance. Both endpoint
crossings lie strictly on their respective sides of the contact. -/
theorem exists_lens_endpoints {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {w R c δ η : ℝ}
    (hδ : 0 < δ) (hR : 0 < R)
    (hcurv : ∀ t ∈ Icc (w - R) (w + R), c ≤ deriv (deriv f) t)
    (hvalue : |f w| ≤ δ) (hslope : |deriv f w| ≤ η)
    (hroom : 2 * δ < c / 2 * R ^ 2 - η * R - δ) :
    ∃ x ∈ Ioo (w - R) w, ∃ y ∈ Ioo w (w + R), f x = 2 * δ ∧ f y = 2 * δ := by
  have hw : w ∈ Icc (w - R) (w + R) := ⟨by linarith, by linarith⟩
  have hl := contact_quadratic_gap hf
    (fun t ht => hcurv t (uIcc_subset_Icc hw (left_mem_Icc.mpr (by linarith)) ht))
    hvalue hslope
  have hr := contact_quadratic_gap hf
    (fun t ht => hcurv t (uIcc_subset_Icc hw (right_mem_Icc.mpr (by linarith)) ht))
    hvalue hslope
  have habsl : |w - R - w| = R := by rw [show w - R - w = -R by ring, abs_neg, abs_of_pos hR]
  have habsr : |w + R - w| = R := by rw [show w + R - w = R by ring, abs_of_pos hR]
  rw [habsl] at hl
  rw [habsr] at hr
  have hleft : 2 * δ < f (w - R) := hroom.trans_le hl
  have hright : 2 * δ < f (w + R) := hroom.trans_le hr
  have hcenter : f w < 2 * δ := by linarith [(abs_le.mp hvalue).2]
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' (by linarith : w - R ≤ w)
    hf.continuous.continuousOn ⟨hcenter.le, hleft.le⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc (by linarith : w ≤ w + R)
    hf.continuous.continuousOn ⟨hcenter.le, hright.le⟩
  refine ⟨x, ⟨?_, ?_⟩, y, ⟨?_, ?_⟩, hfx, hfy⟩
  · exact lt_of_le_of_ne hx.1 (by intro he; have he' := congrArg f he; linarith)
  · exact lt_of_le_of_ne hx.2 (by intro he; have he' := congrArg f he; linarith)
  · exact lt_of_le_of_ne hy.1 (by intro he; have he' := congrArg f he; linarith)
  · exact lt_of_le_of_ne hy.2 (by intro he; have he' := congrArg f he; linarith)

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
