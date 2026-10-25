-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.NormalChart.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from workspace o157, branch x0572 (commit 9dec67f), TubeCoordinates/NormalChart.lean;
-- the cotangent frame and strip code now come from the accepted o213 closure.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.Basic
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CotFrame
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.StripCode

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- Orthogonal point coordinates with first axis `v`. -/
noncomputable def pointChart (v p : Plane) : ℝ × ℝ :=
  (inner ℝ p v, inner ℝ p (perp v))

/-- The slope and intercept of a normal-labelled line in the frame `v`. -/
noncomputable def lineChart (v : Plane) (l : Plane × Plane) : ℝ × ℝ :=
  (cotNormal v l.2, (pointChart v l.1).2 - cotNormal v l.2 * (pointChart v l.1).1)

lemma lineChart_neg_normal (v p e : Plane) :
    lineChart v (p, -e) = lineChart v (p, e) := by
  simp only [lineChart, cotNormal_neg]

lemma lineChart_height_pin (v p e : Plane) :
    height (lineChart v (p, e)) (pointChart v p).1 = (pointChart v p).2 := by
  simp only [height, lineChart]
  ring

/-- Normal incidence equals vertical affine incidence times the transverse
component of the normal. -/
lemma inner_eq_chart_error {v : Plane} (hv : ‖v‖ = 1) (p q e : Plane)
    (he : inner ℝ e (perp v) ≠ 0) :
    inner ℝ (q - p) e = inner ℝ e (perp v) *
      ((pointChart v q).2 - height (lineChart v (p, e)) (pointChart v q).1) := by
  rw [inner_frame hv]
  simp only [pointChart, height, lineChart, cotNormal, inner_sub_left]
  field_simp
  ring

lemma chart_incidence {v p q e : Plane} {r c : ℝ} (hv : ‖v‖ = 1) (hc : 0 < c)
    (he : c ≤ |inner ℝ e (perp v)|) (hinc : |inner ℝ (q - p) e| ≤ r) :
    |(pointChart v q).2 - height (lineChart v (p, e)) (pointChart v q).1| ≤ r / c := by
  have hne : inner ℝ e (perp v) ≠ 0 := by
    intro h
    rw [h, abs_zero] at he
    linarith
  rw [inner_eq_chart_error hv p q e hne, abs_mul] at hinc
  apply (le_div_iff₀ hc).mpr
  calc
    |(pointChart v q).2 - height (lineChart v (p, e)) (pointChart v q).1| * c ≤
        |inner ℝ e (perp v)| *
          |(pointChart v q).2 - height (lineChart v (p, e)) (pointChart v q).1| := by
      nlinarith [abs_nonneg ((pointChart v q).2 - height (lineChart v (p, e)) (pointChart v q).1)]
    _ ≤ r := hinc

/-- Cotangent coordinates control the distance between unoriented normals. -/
lemma normal_distance_of_slope {v e e' : Plane} {c : ℝ} (hv : ‖v‖ = 1)
    (he : ‖e‖ = 1) (he' : ‖e'‖ = 1) (hc : 0 < c)
    (hw : c ≤ |inner ℝ e (perp v)|) (hw' : c ≤ |inner ℝ e' (perp v)|) :
    c * dist e e' ≤ |cotNormal v e - cotNormal v e'| ∨
      c * dist e (-e') ≤ |cotNormal v e - cotNormal v e'| := by
  by_cases hs : 0 ≤ inner ℝ e (perp v)
  · rw [abs_of_nonneg hs] at hw
    by_cases hs' : 0 ≤ inner ℝ e' (perp v)
    · rw [abs_of_nonneg hs'] at hw'
      exact Or.inl (by simpa only [dist_eq_norm] using cotNormal_expanding hv he he' hc hw hw')
    · rw [abs_of_neg (lt_of_not_ge hs')] at hw'
      have hb : c ≤ inner ℝ (-e') (perp v) := by simpa using hw'
      exact Or.inr (by simpa only [dist_eq_norm, cotNormal_neg] using
        cotNormal_expanding hv he (by simpa using he') hc hw hb)
  · rw [abs_of_neg (lt_of_not_ge hs)] at hw
    have ha : c ≤ inner ℝ (-e) (perp v) := by simpa using hw
    by_cases hs' : 0 ≤ inner ℝ e' (perp v)
    · rw [abs_of_nonneg hs'] at hw'
      have hh := cotNormal_expanding hv (by simpa using he) he' hc ha hw'
      have hd : dist (-e) e' = dist e (-e') := by
        simpa only [neg_neg] using dist_neg_neg e (-e')
      rw [← dist_eq_norm, hd, cotNormal_neg] at hh
      exact Or.inr hh
    · rw [abs_of_neg (lt_of_not_ge hs')] at hw'
      have hb : c ≤ inner ℝ (-e') (perp v) := by simpa using hw'
      have hh := cotNormal_expanding hv (by simpa using he) (by simpa using he') hc ha hb
      rw [← dist_eq_norm, dist_neg_neg, cotNormal_neg, cotNormal_neg] at hh
      exact Or.inl hh

lemma chart_offset_bound {v p p' e e' : Plane} (hv : ‖v‖ = 1)
    (he : ‖e‖ = 1) (hne : inner ℝ e (perp v) ≠ 0) (hp' : ‖p'‖ ≤ 4) :
    |inner ℝ (p - p') e| ≤
      |(lineChart v (p, e)).2 - (lineChart v (p', e')).2| +
        4 * |(lineChart v (p, e)).1 - (lineChart v (p', e')).1| := by
  have hi : inner ℝ (p - p') e = inner ℝ e (perp v) *
      (((lineChart v (p, e)).2 - (lineChart v (p', e')).2) +
        ((lineChart v (p, e)).1 - (lineChart v (p', e')).1) * (pointChart v p').1) := by
    have hh := inner_eq_chart_error hv p p' e hne
    have hp := lineChart_height_pin v p' e'
    rw [inner_sub_left] at hh ⊢
    simp only [height] at hh hp
    rw [← hp] at hh
    nlinarith only [hh]
  have hn : |inner ℝ e (perp v)| ≤ 1 := by
    simpa only [he, perp_norm, hv, mul_one] using abs_real_inner_le_norm e (perp v)
  have hx : |(pointChart v p').1| ≤ 4 := by
    have hh := abs_real_inner_le_norm p' v
    simp only [hv, mul_one] at hh
    exact hh.trans hp'
  rw [hi, abs_mul]
  calc
    _ ≤ |((lineChart v (p, e)).2 - (lineChart v (p', e')).2) +
        ((lineChart v (p, e)).1 - (lineChart v (p', e')).1) * (pointChart v p').1| := by
      exact mul_le_of_le_one_left (abs_nonneg _) hn
    _ ≤ |(lineChart v (p, e)).2 - (lineChart v (p', e')).2| +
        |((lineChart v (p, e)).1 - (lineChart v (p', e')).1) * (pointChart v p').1| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul]; nlinarith [abs_nonneg ((lineChart v (p, e)).1 - (lineChart v (p', e')).1)]

/-- The strip separation in the frozen theorem implies ordinary metric
separation of affine line parameters on a transverse chart. -/
theorem lineChart_separated {v : Plane} {l l' : Plane × Plane} {r : ℝ}
    (hv : ‖v‖ = 1) (he : ‖l.2‖ = 1) (he' : ‖l'.2‖ = 1)
    (hp' : ‖l'.1‖ ≤ 4)
    (hw : 1 / 2 ≤ |inner ℝ l.2 (perp v)|)
    (hw' : 1 / 2 ≤ |inner ℝ l'.2 (perp v)|) (hsep : StripSep r l l') :
    r / 10 ≤ dist (lineChart v l) (lineChart v l') := by
  by_contra h
  have hlt : dist (lineChart v l) (lineChart v l') < r / 10 := lt_of_not_ge h
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hlt
  have hne : inner ℝ l.2 (perp v) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hw
    norm_num at hw
  rcases hsep with hdir | hoff
  · have hd := normal_distance_of_slope hv he he' (by norm_num : (0 : ℝ) < 1 / 2) hw hw'
    change (1 / 2 : ℝ) * dist l.2 l'.2 ≤ |(lineChart v l).1 - (lineChart v l').1| ∨
      (1 / 2 : ℝ) * dist l.2 (-l'.2) ≤ |(lineChart v l).1 - (lineChart v l').1| at hd
    rcases hd with hd | hd <;> linarith [dist_nonneg (x := lineChart v l) (y := lineChart v l')]
  · have hb := chart_offset_bound (p := l.1) (e' := l'.2) hv he hne hp'
    change |inner ℝ (l.1 - l'.1) l.2| ≤
      |(lineChart v l).2 - (lineChart v l').2| + 4 * |(lineChart v l).1 - (lineChart v l').1| at hb
    linarith [dist_nonneg (x := lineChart v l) (y := lineChart v l')]

/-- A normal in a small arc about the vertical axis has small affine slope. -/
lemma slope_bound_of_normal_arc {v e : Plane} {Δ : ℝ} (hv : ‖v‖ = 1)
    (hΔ : Δ ≤ 1) (hd : dist e (perp v) ≤ Δ / 2) :
    1 / 2 ≤ inner ℝ e (perp v) ∧ |cotNormal v e| ≤ Δ := by
  have hperp : inner ℝ (perp v) v = 0 := by rw [real_inner_comm]; exact perp_inner v
  have hself : inner ℝ (perp v) (perp v) = 1 := by
    rw [real_inner_self_eq_norm_sq, perp_norm, hv]
    norm_num
  have ha : |inner ℝ e v| ≤ Δ / 2 := by
    have hh := abs_real_inner_le_norm (e - perp v) v
    rw [hv, mul_one, inner_sub_left, hperp, sub_zero, ← dist_eq_norm] at hh
    exact hh.trans hd
  have hb : |inner ℝ e (perp v) - 1| ≤ Δ / 2 := by
    have hh := abs_real_inner_le_norm (e - perp v) (perp v)
    rw [perp_norm, hv, mul_one, inner_sub_left, hself, ← dist_eq_norm] at hh
    exact hh.trans hd
  have hw : 1 / 2 ≤ inner ℝ e (perp v) := by
    have := (abs_le.mp hb).1
    linarith
  refine ⟨hw, ?_⟩
  have hΔ0 : 0 ≤ Δ := by linarith [dist_nonneg (x := e) (y := perp v)]
  have hw0 : 0 < inner ℝ e (perp v) := by linarith
  rw [cotNormal, abs_div, abs_neg, abs_of_pos hw0, div_le_iff₀ hw0]
  nlinarith

lemma rescale_dist {Δ : ℝ} (hΔ : 0 < Δ) (l l' : ℝ × ℝ) :
    dist (rescale Δ l) (rescale Δ l') = dist l l' / Δ := by
  simp only [Prod.dist_eq, rescale, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hΔ]
  exact max_div_div_right hΔ.le _ _

/-- Anisotropic rescaling magnifies the separation of line parameters. -/
lemma rescaled_lineChart_separated {v : Plane} {l l' : Plane × Plane} {r Δ : ℝ}
    (hΔ : 0 < Δ) (hv : ‖v‖ = 1) (he : ‖l.2‖ = 1) (he' : ‖l'.2‖ = 1)
    (hp' : ‖l'.1‖ ≤ 4)
    (hw : 1 / 2 ≤ |inner ℝ l.2 (perp v)|)
    (hw' : 1 / 2 ≤ |inner ℝ l'.2 (perp v)|) (hsep : StripSep r l l') :
    r / (10 * Δ) ≤ dist (rescale Δ (lineChart v l)) (rescale Δ (lineChart v l')) := by
  rw [rescale_dist hΔ, ← div_div]
  exact div_le_div_of_nonneg_right (lineChart_separated hv he he' hp' hw hw' hsep) hΔ.le

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
