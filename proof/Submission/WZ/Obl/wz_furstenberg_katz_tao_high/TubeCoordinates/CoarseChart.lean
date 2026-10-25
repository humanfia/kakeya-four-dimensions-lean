-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.CoarseChart.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, TubeCoordinates/CoarseChart.lean; accepted imports updated.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.NormalChart

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- The transverse cotangent chart is Lipschitz on unit normals. -/
lemma cotNormal_dist_bound {v e e' : Plane} (hv : ‖v‖ = 1) (he' : ‖e'‖ = 1)
    (hw : 1 / 2 ≤ |inner ℝ e (perp v)|)
    (hw' : 1 / 2 ≤ |inner ℝ e' (perp v)|) :
    |cotNormal v e - cotNormal v e'| ≤ 8 * dist e e' := by
  let a := inner ℝ e v
  let a' := inner ℝ e' v
  let b := inner ℝ e (perp v)
  let b' := inner ℝ e' (perp v)
  have hb : b ≠ 0 := by intro h; simp only [b] at h; rw [h, abs_zero] at hw; norm_num at hw
  have hb' : b' ≠ 0 := by intro h; simp only [b'] at h; rw [h, abs_zero] at hw'; norm_num at hw'
  have ha' : |a'| ≤ 1 := by
    simpa [a', he', hv] using abs_real_inner_le_norm e' v
  have hbb' : |b'| ≤ 1 := by
    simpa [b', he', hv, perp_norm] using abs_real_inner_le_norm e' (perp v)
  have hab : |a' - a| ≤ dist e e' := by
    have hh := abs_real_inner_le_norm (e' - e) v
    simpa only [inner_sub_left, hv, mul_one, ← dist_eq_norm, dist_comm] using hh
  have hbb : |b - b'| ≤ dist e e' := by
    have hh := abs_real_inner_le_norm (e - e') (perp v)
    simpa only [inner_sub_left, perp_norm, hv, mul_one, ← dist_eq_norm] using hh
  have hdet : (cotNormal v e - cotNormal v e') * (b * b') = a' * b - a * b' := by
    change (-a / b - -a' / b') * (b * b') = _
    field_simp
    ring
  have hnum : |a' * b - a * b'| ≤ 2 * dist e e' := by
    calc
      _ = |a' * (b - b') + (a' - a) * b'| := by congr 1; ring
      _ ≤ |a' * (b - b')| + |(a' - a) * b'| := abs_add_le _ _
      _ = |a'| * |b - b'| + |a' - a| * |b'| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * dist e e' + dist e e' * 1 := by gcongr
      _ = _ := by ring
  have hden : (1 / 4 : ℝ) ≤ |b| * |b'| := by
    have hh := mul_le_mul hw hw' (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_nonneg _)
    norm_num at hh
    exact hh
  have hh := congrArg abs hdet
  rw [abs_mul, abs_mul] at hh
  have hd := mul_le_mul_of_nonneg_left hden (abs_nonneg (cotNormal v e - cotNormal v e'))
  nlinarith

/-- Nearby normals and nearby offsets give nearby affine line parameters. -/
lemma lineChart_dist_bound {v p p' e e' : Plane} (hv : ‖v‖ = 1)
    (he' : ‖e'‖ = 1) (hp' : ‖p'‖ ≤ 4)
    (hw : 1 / 2 ≤ |inner ℝ e (perp v)|)
    (hw' : 1 / 2 ≤ |inner ℝ e' (perp v)|) :
    dist (lineChart v (p, e)) (lineChart v (p', e')) ≤
      2 * |inner ℝ (p - p') e| + 32 * dist e e' := by
  have hcot := cotNormal_dist_bound hv he' hw hw'
  have hx : |(pointChart v p').1| ≤ 4 := by
    have hh := abs_real_inner_le_norm p' v
    simp only [hv, mul_one] at hh
    exact hh.trans hp'
  have hi := chart_incidence (p := p) (q := p') hv (by norm_num : (0 : ℝ) < 1 / 2) hw
    (le_refl |inner ℝ (p' - p) e|)
  have heq : |inner ℝ (p' - p) e| = |inner ℝ (p - p') e| := by
    simp only [inner_sub_left]
    exact abs_sub_comm _ _
  rw [heq] at hi
  have hi' : |(pointChart v p').2 - height (lineChart v (p, e)) (pointChart v p').1| ≤
      2 * |inner ℝ (p - p') e| := by convert hi using 1 <;> ring
  have hb : |(lineChart v (p, e)).2 - (lineChart v (p', e')).2| ≤
      2 * |inner ℝ (p - p') e| + 32 * dist e e' := by
    calc
      _ = |-((pointChart v p').2 - height (lineChart v (p, e)) (pointChart v p').1) -
          (cotNormal v e - cotNormal v e') * (pointChart v p').1| := by
        congr 1
        simp only [lineChart, height]
        ring
      _ ≤ |-((pointChart v p').2 - height (lineChart v (p, e)) (pointChart v p').1)| +
          |(cotNormal v e - cotNormal v e') * (pointChart v p').1| := abs_sub _ _
      _ ≤ 2 * |inner ℝ (p - p') e| + (8 * dist e e') * 4 := by
        rw [abs_neg, abs_mul]
        exact add_le_add hi' (mul_le_mul hcot hx (abs_nonneg _) (by positivity))
      _ = _ := by ring
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  exact ⟨hcot.trans (by linarith [abs_nonneg (inner ℝ (p - p') e), dist_nonneg (x := e) (y := e')]), hb⟩

/-- Separation of coarse affine parameters supplies the strip separation
needed by the quadratic coarse-incidence estimate. -/
theorem stripSep_of_lineChart_separated {v : Plane} {l l' : Plane × Plane} {r : ℝ}
    (hr : 0 < r) (hv : ‖v‖ = 1) (he' : ‖l'.2‖ = 1) (hp' : ‖l'.1‖ ≤ 4)
    (hw : 1 / 2 ≤ |inner ℝ l.2 (perp v)|)
    (hw' : 1 / 2 ≤ |inner ℝ l'.2 (perp v)|)
    (hsep : 40 * r ≤ dist (lineChart v l) (lineChart v l')) :
    StripSep r l l' := by
  by_cases hoff : r ≤ |inner ℝ (l.1 - l'.1) l.2|
  · exact Or.inr hoff
  have hoff' := lt_of_not_ge hoff
  left
  constructor
  · by_contra hd
    have hd' := lt_of_not_ge hd
    have hb := lineChart_dist_bound (p := l.1) hv he' hp' hw hw'
    change dist (lineChart v l) (lineChart v l') ≤ _ at hb
    linarith
  · by_contra hd
    have hd' := lt_of_not_ge hd
    have hwneg : 1 / 2 ≤ |inner ℝ (-l'.2) (perp v)| := by simpa using hw'
    have hb := lineChart_dist_bound (p := l.1) hv (by simpa using he') hp' hw hwneg
    rw [lineChart_neg_normal] at hb
    change dist (lineChart v l) (lineChart v l') ≤ _ at hb
    linarith

/-- A coarse representative covers every fine incidence in its parameter cell. -/
lemma chart_incidence_of_parameter_close {v p p' e e' y : Plane} {r R : ℝ}
    (hv : ‖v‖ = 1) (he' : ‖e'‖ = 1) (hy : ‖y‖ ≤ 4)
    (hw : 1 / 2 ≤ |inner ℝ e (perp v)|)
    (hw' : inner ℝ e' (perp v) ≠ 0)
    (hinc : |inner ℝ (y - p) e| ≤ r)
    (hclose : dist (lineChart v (p, e)) (lineChart v (p', e')) ≤ R) :
    |inner ℝ (y - p') e'| ≤ 2 * r + 5 * R := by
  have hi := chart_incidence hv (by norm_num : (0 : ℝ) < 1 / 2) hw hinc
  have hx : |(pointChart v y).1| ≤ 4 := by
    have hh := abs_real_inner_le_norm y v
    simp only [hv, mul_one] at hh
    exact hh.trans hy
  have hec : |inner ℝ e' (perp v)| ≤ 1 := by
    simpa only [he', perp_norm, hv, mul_one] using abs_real_inner_le_norm e' (perp v)
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hclose
  rw [inner_eq_chart_error hv p' y e' hw', abs_mul]
  apply le_trans (mul_le_of_le_one_left (abs_nonneg _) hec)
  have heq : (pointChart v y).2 - height (lineChart v (p', e')) (pointChart v y).1 =
      ((pointChart v y).2 - height (lineChart v (p, e)) (pointChart v y).1) +
      (((lineChart v (p, e)).1 - (lineChart v (p', e')).1) * (pointChart v y).1 +
        ((lineChart v (p, e)).2 - (lineChart v (p', e')).2)) := by
    simp only [height]
    ring
  rw [heq]
  calc
    _ ≤ |(pointChart v y).2 - height (lineChart v (p, e)) (pointChart v y).1| +
        |((lineChart v (p, e)).1 - (lineChart v (p', e')).1) * (pointChart v y).1 +
        ((lineChart v (p, e)).2 - (lineChart v (p', e')).2)| := abs_add_le _ _
    _ ≤ r / (1 / 2) +
        (|((lineChart v (p, e)).1 - (lineChart v (p', e')).1) * (pointChart v y).1| +
        |((lineChart v (p, e)).2 - (lineChart v (p', e')).2)|) := add_le_add hi (abs_add_le _ _)
    _ ≤ r / (1 / 2) + (R * 4 + R) := by
      rw [abs_mul]
      exact add_le_add le_rfl (add_le_add
        (mul_le_mul hclose.1 hx (abs_nonneg _) ((abs_nonneg _).trans hclose.1)) hclose.2)
    _ = _ := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
