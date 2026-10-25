-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.StationaryContact.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LensGeometry

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- A positive lower curvature bound gives a quantitative increase of the slope. -/
theorem curvature_slope_gap {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {l u x y c : ℝ} (hx : x ∈ Icc l u) (hy : y ∈ Icc l u) (hxy : x ≤ y)
    (hcurv : ∀ t ∈ Icc l u, c ≤ deriv (deriv f) t) :
    c * (y - x) ≤ deriv f y - deriv f x := by
  have hd : Differentiable ℝ (deriv f) :=
    (hf.deriv' (n := 1)).differentiable (by norm_num)
  exact (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv
    hd.continuous.continuousOn hd.differentiableOn
    (fun t ht => hcurv t (interior_subset ht)) x hx y hy hxy

/-- Distance to a stationary point is bounded by the local slope divided by
its lower curvature bound. This needs no continuity modulus for curvature. -/
theorem dist_stationary_le_slope {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {l u x y c : ℝ} (hc : 0 < c)
    (hx : x ∈ Icc l u) (hy : y ∈ Icc l u)
    (hcurv : ∀ t ∈ Icc l u, c ≤ deriv (deriv f) t)
    (hstationary : deriv f y = 0) :
    |x - y| ≤ |deriv f x| / c := by
  apply (le_div_iff₀ hc).mpr
  rcases le_total x y with hxy | hyx
  · have h := curvature_slope_gap hf hx hy hxy hcurv
    rw [hstationary] at h
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    nlinarith [neg_abs_le (deriv f x)]
  · have h := curvature_slope_gap hf hy hx hyx hcurv
    rw [hstationary] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    nlinarith [le_abs_self (deriv f x)]

/-- An approximate stationary point with enough room on both sides determines
a unique exact stationary point, with displacement at most `eta / c`. -/
theorem exists_unique_stationary_near {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {w R c η : ℝ} (hc : 0 < c) (hR : 0 ≤ R)
    (hcurv : ∀ t ∈ Icc (w - R) (w + R), c ≤ deriv (deriv f) t)
    (hslope : |deriv f w| ≤ η) (hroom : η ≤ c * R) :
    ∃ x ∈ Icc (w - R) (w + R), deriv f x = 0 ∧
      |x - w| ≤ η / c ∧
      ∀ y ∈ Icc (w - R) (w + R), deriv f y = 0 → y = x := by
  have hw : w ∈ Icc (w - R) (w + R) := ⟨by linarith, by linarith⟩
  have hl : w - R ∈ Icc (w - R) (w + R) := ⟨le_rfl, by linarith⟩
  have hr : w + R ∈ Icc (w - R) (w + R) := ⟨by linarith, le_rfl⟩
  have hleft := curvature_slope_gap hf hl hw (by linarith) hcurv
  have hright := curvature_slope_gap hf hw hr (by linarith) hcurv
  have hleft0 : deriv f (w - R) ≤ 0 := by
    linarith [(abs_le.mp hslope).2]
  have hright0 : 0 ≤ deriv f (w + R) := by
    linarith [(abs_le.mp hslope).1]
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (by linarith : w - R ≤ w + R)
    (hf.deriv' (n := 1)).continuous.continuousOn ⟨hleft0, hright0⟩
  refine ⟨x, hx, hfx, ?_, ?_⟩
  · rw [abs_sub_comm]
    exact (dist_stationary_le_slope hf hc hw hx hcurv hfx).trans
      (div_le_div_of_nonneg_right hslope hc.le)
  · intro y hy hfy
    have h := dist_stationary_le_slope hf hc hy hx hcurv hfx
    rw [hfy, abs_zero, zero_div] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- The loss in value on moving to a stationary point is quadratic in the
initial slope. Only a lower curvature bound is required. -/
theorem stationary_value_drop_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {l u w x c : ℝ} (hc : 0 < c)
    (hw : w ∈ Icc l u) (hx : x ∈ Icc l u)
    (hcurv : ∀ t ∈ Icc l u, c ≤ deriv (deriv f) t)
    (hstationary : deriv f x = 0) :
    0 ≤ f w - f x ∧ f w - f x ≤ (deriv f w) ^ 2 / (2 * c) := by
  have hmin := quadratic_gap_of_curvature hf
    (fun t ht => hcurv t (uIcc_subset_Icc hx hw ht))
  rw [hstationary, zero_mul, add_zero] at hmin
  have hquad := quadratic_gap_of_curvature hf
    (fun t ht => hcurv t (uIcc_subset_Icc hw hx ht))
  refine ⟨?_, ?_⟩
  · have hn : 0 ≤ c / 2 * (w - x) ^ 2 := by positivity
    linarith
  · apply (le_div_iff₀ (by positivity : 0 < 2 * c)).mpr
    have hh := mul_le_mul_of_nonneg_left hquad (by positivity : 0 ≤ 2 * c)
    nlinarith only [hh, sq_nonneg (c * (x - w) + deriv f w)]

/-- The critical value differs from an approximate contact value by at most
its quadratic slope error. The exact stationary point is a minimum on the
entire interval. -/
theorem stationary_value_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {l u w x c δ η : ℝ} (hc : 0 < c)
    (hw : w ∈ Icc l u) (hx : x ∈ Icc l u)
    (hcurv : ∀ t ∈ Icc l u, c ≤ deriv (deriv f) t)
    (hvalue : |f w| ≤ δ) (hslope : |deriv f w| ≤ η)
    (hstationary : deriv f x = 0) :
    -δ - η ^ 2 / (2 * c) ≤ f x ∧ f x ≤ δ ∧
      ∀ y ∈ Icc l u, f x + c / 2 * (y - x) ^ 2 ≤ f y := by
  have hη : 0 ≤ η := (abs_nonneg _).trans hslope
  have hmin : ∀ y ∈ Icc l u, f x + c / 2 * (y - x) ^ 2 ≤ f y := by
    intro y hy
    simpa only [hstationary, zero_mul, add_zero] using
      quadratic_gap_of_curvature hf
        (fun t ht => hcurv t (uIcc_subset_Icc hx hy ht))
  have hlow := contact_quadratic_gap hf
    (fun t ht => hcurv t (uIcc_subset_Icc hw hx ht)) hvalue hslope
  have hcomplete : -(η ^ 2 / (2 * c)) ≤
      c / 2 * |x - w| ^ 2 - η * |x - w| := by
    rw [← neg_div, div_le_iff₀ (by positivity : 0 < 2 * c)]
    nlinarith only [sq_nonneg (c * |x - w| - η)]
  refine ⟨by linarith, ?_, hmin⟩
  have hh := hmin w hw
  have hn : 0 ≤ c / 2 * (w - x) ^ 2 := by positivity
  linarith [(abs_le.mp hvalue).2]

/-- Exact contact times vary Lipschitzly with one coefficient while the
opposite curve and the uniformly positive curvature window stay fixed. -/
theorem stationary_contact_time_stability {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j : Fin n) {l u x y c : ℝ} (hc : 0 < c)
    (hI : Icc l u ⊆ Icc (-1 : ℝ) 1)
    (hx : x ∈ Icc l u) (hy : y ∈ Icc l u)
    (hcurv : ∀ t ∈ Icc l u,
      c ≤ deriv (deriv (g k)) t - deriv (deriv (g j)) t)
    (hix : deriv (g i) x = deriv (g j) x)
    (hky : deriv (g k) y = deriv (g j) y) :
    |x - y| ≤ 19 * dist (q i) (q k) / c := by
  have ht := dist_stationary_le_slope (f := g k - g j) ((hg k).sub (hg j)) hc hx hy
    (by simpa only [deriv2_sub_of_contDiff_two (hg k) (hg j), Pi.sub_apply] using hcurv)
    (by simp only [deriv_sub_of_contDiff_two (hg k) (hg j), Pi.sub_apply, hky, sub_self])
  apply ht.trans
  apply div_le_div_of_nonneg_right _ hc.le
  rw [deriv_sub_of_contDiff_two (hg k) (hg j)]
  change |deriv (g k) x - deriv (g j) x| ≤ _
  rw [← hix, abs_sub_comm]
  exact (deriv_le_jetDistance (g i) (g k) x).trans (hjet i k x (hI hx)).2

/-- Moving the first curve changes a critical contact value by its value
change at the old critical time, with a one-sided quadratic remainder. -/
theorem stationary_contact_value_stability {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j : Fin n) {l u x y c : ℝ} (hc : 0 < c)
    (hI : Icc l u ⊆ Icc (-1 : ℝ) 1)
    (hx : x ∈ Icc l u) (hy : y ∈ Icc l u)
    (hcurv : ∀ t ∈ Icc l u,
      c ≤ deriv (deriv (g k)) t - deriv (deriv (g j)) t)
    (hix : deriv (g i) x = deriv (g j) x)
    (hky : deriv (g k) y = deriv (g j) y) :
    0 ≤ (g i x - g j x) - (g k y - g j y) - (g i x - g k x) ∧
      (g i x - g j x) - (g k y - g j y) - (g i x - g k x) ≤
        (19 * dist (q i) (q k)) ^ 2 / (2 * c) := by
  have hdrop := stationary_value_drop_le (f := g k - g j)
    ((hg k).sub (hg j)) hc hx hy
    (by simpa only [deriv2_sub_of_contDiff_two (hg k) (hg j), Pi.sub_apply] using hcurv)
    (by simp only [deriv_sub_of_contDiff_two (hg k) (hg j), Pi.sub_apply, hky, sub_self])
  have hs : |deriv (g k - g j) x| ≤ 19 * dist (q i) (q k) := by
    rw [deriv_sub_of_contDiff_two (hg k) (hg j)]
    change |deriv (g k) x - deriv (g j) x| ≤ _
    rw [← hix, abs_sub_comm]
    exact (deriv_le_jetDistance (g i) (g k) x).trans (hjet i k x (hI hx)).2
  have hsq : (deriv (g k - g j) x) ^ 2 ≤ (19 * dist (q i) (q k)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs 2
  have hb := hdrop.2.trans (div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 2 * c))
  simp only [Pi.sub_apply] at hdrop hb
  constructor <;> linarith [hdrop.1]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
