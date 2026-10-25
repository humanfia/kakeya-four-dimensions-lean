-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.LensLocation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.CrossingIntervals
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.CurvatureOrder

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- Two level crossings eliminate the value and slope alternatives, forcing
the uniform curvature alternative on the whole short window. -/
theorem curvature_separated_of_two_crossings {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {l u a b v : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hab : a < b)
    (hv : |v| < dist (q i) (q j) / 480)
    (heqa : g i a - g j a = v) (heqb : g i b - g j b = v) :
    ∀ t ∈ Icc l u,
      dist (q i) (q j) / 60 ≤ |deriv (deriv (g i)) t - deriv (deriv (g j)) t| := by
  have hmem {t : ℝ} (ht : t ∈ Icc l u) : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨hl.trans ht.1, ht.2.trans hu⟩
  have hclose {t : ℝ} (ht : t ∈ Icc l u) : |t - l| ≤ 1 / 10000 := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hlmem : l ∈ Icc (-1 : ℝ) 1 := ⟨hl, ha.1.trans (ha.2.trans hu)⟩
  rcases hjet.local_alternative hg i j hlmem with hval | hslope | hcurv
  · have h := hval a (hmem ha) (hclose ha)
    rw [heqa] at h
    exact (not_lt.mpr h hv).elim
  · have hf : ContDiff ℝ 2 (g i - g j) := (hg i).sub (hg j)
    obtain ⟨t, ht, het⟩ := exists_deriv_eq_zero hab hf.continuous.continuousOn
      (show (g i - g j) a = (g i - g j) b from heqa.trans heqb.symm)
    have htmem : t ∈ Icc l u := ⟨ha.1.trans ht.1.le, ht.2.le.trans hb.2⟩
    have h := hslope t (hmem htmem) (hclose htmem)
    rw [deriv_sub_of_contDiff_two (hg i) (hg j)] at het
    change deriv (g i) t - deriv (g j) t = 0 at het
    rw [het, abs_zero] at h
    have := abs_nonneg v
    exfalso
    linarith
  · exact fun t ht => hcurv t (hmem ht) (hclose ht)

/-- A negative value of a convex function lies strictly between any two
of its zero values, whenever all three times lie in its convex domain. -/
theorem negative_mem_lens_of_convex {f : ℝ → ℝ} {S : Set ℝ} {a b x : ℝ}
    (hf : ConvexOn ℝ S f) (ha : a ∈ S) (hb : b ∈ S) (hx : x ∈ S)
    (hab : a < b) (heqa : f a = 0) (heqb : f b = 0) (hfx : f x < 0) :
    x ∈ Ioo a b := by
  have hxa : x ≠ a := by intro he; subst x; linarith
  have hxb : x ≠ b := by intro he; subst x; linarith
  constructor
  · by_contra h
    have hxa' : x < a := lt_of_le_of_ne (le_of_not_gt h) hxa
    have h := hf.slope_mono_adjacent hx hb hxa' hab
    rw [heqa, heqb] at h
    have hpos : 0 < (0 - f x) / (a - x) := div_pos (by linarith) (sub_pos.mpr hxa')
    have hzero : (0 - f x) / (a - x) ≤ 0 := by simpa using h
    exact (not_lt.mpr hzero) hpos
  · by_contra h
    have hbx : b < x := lt_of_le_of_ne (le_of_not_gt h) hxb.symm
    have h := hf.slope_mono_adjacent ha hx hab hbx
    rw [heqa, heqb] at h
    have hneg : (f x - 0) / (x - b) < 0 := div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr hbx)
    have hzero : 0 ≤ (f x - 0) / (x - b) := by simpa using h
    exact (not_lt.mpr hzero) hneg

/-- Two crossings give a uniformly convex or uniformly concave curve
 difference throughout the short window, without a curvature modulus. -/
theorem convex_or_concave_of_two_crossings {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {l u a b v : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hab : a < b)
    (hv : |v| < dist (q i) (q j) / 480)
    (heqa : g i a - g j a = v) (heqb : g i b - g j b = v) :
    StrictConvexOn ℝ (Icc l u) (g i - g j) ∨
      StrictConcaveOn ℝ (Icc l u) (g i - g j) := by
  have hsep := curvature_separated_of_two_crossings hg hjet i j
    hl hu hshort ha hb hab hv heqa heqb
  have hdist : 0 < dist (q i) (q j) := by
    have := abs_nonneg v
    linarith
  have hcont : Continuous (fun t => deriv (deriv (g i)) t - deriv (deriv (g j)) t) :=
    ((((hg i).deriv' (n := 1)).deriv' (n := 0)).continuous).sub
      ((((hg j).deriv' (n := 1)).deriv' (n := 0)).continuous)
  have hf : ContDiff ℝ 2 (g i - g j) := (hg i).sub (hg j)
  rcases continuous_abs_lower_sign (convex_Icc l u).isPreconnected
      hcont.continuousOn (by positivity : 0 < dist (q i) (q j) / 60) hsep with
    hpos | hneg
  · left
    apply strictConvexOn_of_deriv2_pos' (convex_Icc l u) hf.continuous.continuousOn
    intro t ht
    have h := hpos t ht
    change 0 < deriv (deriv (g i - g j)) t
    rw [deriv2_sub_of_contDiff_two (hg i) (hg j)]
    change 0 < deriv (deriv (g i)) t - deriv (deriv (g j)) t
    linarith
  · right
    apply strictConcaveOn_of_deriv2_neg' (convex_Icc l u) hf.continuous.continuousOn
    intro t ht
    have h := hneg t ht
    change deriv (deriv (g i - g j)) t < 0
    rw [deriv2_sub_of_contDiff_two (hg i) (hg j)]
    change deriv (deriv (g i)) t - deriv (deriv (g j)) t < 0
    linarith

/-- Opposite strict signs place at least one point inside the unique
same-color lens. The uniform jet alternative excludes a tangential zero. -/
theorem one_mem_lens_of_opposite_signs {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j : Fin n) {l u a b x y : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u - l ≤ 1 / 10000)
    (ha : a ∈ Icc l u) (hb : b ∈ Icc l u) (hab : a < b)
    (hdist : 0 < dist (q i) (q j))
    (heqa : g i a = g j a) (heqb : g i b = g j b)
    (hx : x ∈ Icc l u) (hy : y ∈ Icc l u)
    (hxsign : g i x - g j x < 0) (hysign : 0 < g i y - g j y) :
    x ∈ Ioo a b ∨ y ∈ Ioo a b := by
  rcases convex_or_concave_of_two_crossings hg hjet i j hl hu hshort ha hb hab
      (v := 0) (by rw [abs_zero]; positivity) (sub_eq_zero.mpr heqa)
      (sub_eq_zero.mpr heqb) with hconv | hconc
  · exact Or.inl (negative_mem_lens_of_convex hconv.convexOn ha hb hx hab
      (sub_eq_zero.mpr heqa) (sub_eq_zero.mpr heqb) hxsign)
  · right
    apply negative_mem_lens_of_convex hconc.neg.convexOn ha hb hy hab
    · simp only [Pi.neg_apply, Pi.sub_apply, heqa, sub_self, neg_zero]
    · simp only [Pi.neg_apply, Pi.sub_apply, heqb, sub_self, neg_zero]
    · change -(g i y - g j y) < 0
      linarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
