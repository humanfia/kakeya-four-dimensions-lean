-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.LensWidth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LensGeometry

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- A function vanishing at the endpoints lies below the parabola with
second derivative `-M` and the same endpoint values. -/
theorem twice_value_le_curvature_mul_gaps {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {l u x M : ℝ} (hx : x ∈ Icc l u) (hl : f l = 0) (hu : f u = 0)
    (hcurv : ∀ t ∈ Icc l u, -M ≤ deriv (deriv f) t) :
    2 * f x ≤ M * (x-l) * (u-x) := by
  by_cases hlu : l = u
  · have hxl : x = l := by have := hx.1; have := hx.2; linarith
    simp [hxl, hl]
  have hlu' : 0 < u-l := sub_pos.mpr (lt_of_le_of_ne (hx.1.trans hx.2) hlu)
  have hleft := quadratic_gap_of_curvature hf
    (fun t ht => hcurv t (uIcc_subset_Icc hx ⟨le_rfl, hx.1.trans hx.2⟩ ht))
  have hright := quadratic_gap_of_curvature hf
    (fun t ht => hcurv t (uIcc_subset_Icc hx ⟨hx.1.trans hx.2, le_rfl⟩ ht))
  rw [hl] at hleft
  rw [hu] at hright
  have ha := mul_le_mul_of_nonneg_right hleft (sub_nonneg.mpr hx.2)
  have hb := mul_le_mul_of_nonneg_right hright (sub_nonneg.mpr hx.1)
  have hh : (u-l) * (2*f x - M*(x-l)*(u-x)) ≤ 0 := by nlinarith only [ha, hb]
  have hzero : 2 * f x - M * (x-l) * (u-x) ≤ 0 :=
    (mul_le_mul_iff_right₀ hlu').mp (by simpa only [mul_zero] using hh)
  linarith

/-- The interpolation error between two zero values is controlled by the
second derivative and the product of distances to the endpoints. -/
theorem twice_abs_value_le_curvature_mul_gaps {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {l u x M : ℝ} (hx : x ∈ Icc l u) (hl : f l = 0) (hu : f u = 0)
    (hcurv : ∀ t ∈ Icc l u, |deriv (deriv f) t| ≤ M) :
    2 * |f x| ≤ M * (x-l) * (u-x) := by
  have hp := twice_value_le_curvature_mul_gaps hf hx hl hu
    (fun t ht => (abs_le.mp (hcurv t ht)).1)
  have hn := twice_value_le_curvature_mul_gaps hf.neg hx
    (by simpa using congrArg Neg.neg hl) (by simpa using congrArg Neg.neg hu)
    (M := M) (by
      intro t ht
      change -M ≤ deriv (deriv (-f)) t
      rw [deriv.neg']
      change -M ≤ deriv (-deriv f) t
      rw [deriv.neg]
      change -M ≤ - deriv (deriv f) t
      linarith [(abs_le.mp (hcurv t ht)).2])
  rcases le_total 0 (f x) with h | h
  · simpa [abs_of_nonneg h] using hp
  · simpa [abs_of_nonpos h] using hn

/-- The depth of a lens is at most one eighth of its curvature bound times
the square of its width. -/
theorem eight_abs_value_le_curvature_mul_width_sq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {l u x M : ℝ} (hx : x ∈ Icc l u) (hl : f l = 0) (hu : f u = 0)
    (hcurv : ∀ t ∈ Icc l u, |deriv (deriv f) t| ≤ M) :
    8 * |f x| ≤ M * (u-l)^2 := by
  have h := twice_abs_value_le_curvature_mul_gaps hf hx hl hu hcurv
  have hM : 0 ≤ M := (abs_nonneg _).trans (hcurv x hx)
  have hquad := mul_nonneg hM (sq_nonneg (2*x-l-u))
  nlinarith

/-- If two curves contact a common lower-curvature curve, any lens between
them containing the first contact must be wide enough to account for the
separation of the contact times. Both contact errors are retained. -/
theorem two_contacts_lens_width {f g b : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hb : ContDiff ℝ 2 b)
    {l u x y c M δ η : ℝ} (hx : x ∈ Icc l u)
    (hl : f l = g l) (hu : f u = g u)
    (hcurv : ∀ t ∈ Icc l u, |deriv (deriv f) t - deriv (deriv g) t| ≤ M)
    (hcross : ∀ t ∈ uIcc y x, c ≤ deriv (deriv g) t - deriv (deriv b) t)
    (hfx : NearContact δ η f b x) (hgy : NearContact δ η g b y) :
    4*c*(x-y)^2 ≤ M*(u-l)^2 + 8*η*|x-y| + 16*δ := by
  have hgap := contact_quadratic_gap (f := g-b) (x := y) (y := x) (c := c)
    (δ := δ) (η := η) (hg.sub hb)
    (by simpa only [deriv2_sub_of_contDiff_two hg hb, Pi.sub_apply] using hcross)
    hgy.1 (by simpa only [deriv_sub_of_contDiff_two hg hb, Pi.sub_apply] using hgy.2)
  have hwidth := eight_abs_value_le_curvature_mul_width_sq (f := g-f) (M := M) (hg.sub hf) hx
    (sub_eq_zero.mpr hl.symm) (sub_eq_zero.mpr hu.symm)
    (by simpa only [deriv2_sub_of_contDiff_two hg hf, Pi.sub_apply, abs_sub_comm] using hcurv)
  simp only [Pi.sub_apply, sq_abs] at hgap hwidth
  have hvalue := (abs_le.mp hfx.1).2
  have habs := le_abs_self (g x-f x)
  nlinarith

/-- The lens-width inequality specialized to the frozen upper jet bound and
the cross-curvature bound supplied by `cluster_curvature_order`. -/
theorem coefficient_two_contacts_lens_width {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j : Fin n) {l u x y D δ η : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hx : x ∈ Icc l u)
    (heql : g i l = g k l) (hequ : g i u = g k u)
    (hcross : ∀ t ∈ uIcc y x,
      D/120 ≤ deriv (deriv (g k)) t - deriv (deriv (g j)) t)
    (hix : NearContact δ η (g i) (g j) x)
    (hky : NearContact δ η (g k) (g j) y) :
    D*(x-y)^2 ≤ 570*dist (q i) (q k)*(u-l)^2 + 240*η*|x-y| + 480*δ := by
  have h := two_contacts_lens_width (hg i) (hg k) (hg j) hx heql hequ
    (fun t ht => (deriv2_le_jetDistance (g i) (g k) t).trans
      (hjet i k t ⟨hl.trans ht.1, ht.2.trans hu⟩).2) hcross hix hky
  nlinarith

/-- When the contact errors are below the quadratic separation scale, the
coefficient distance times lens width squared controls the contact gap. -/
theorem coefficient_contact_gap_sq_le_lens_width_sq {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j : Fin n) {l u x y D δ η : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hx : x ∈ Icc l u)
    (heql : g i l = g k l) (hequ : g i u = g k u)
    (hcross : ∀ t ∈ uIcc y x,
      D/120 ≤ deriv (deriv (g k)) t - deriv (deriv (g j)) t)
    (hix : NearContact δ η (g i) (g j) x)
    (hky : NearContact δ η (g k) (g j) y)
    (herror : 480*η*|x-y| + 960*δ ≤ D*(x-y)^2) :
    D*(x-y)^2 ≤ 1140*dist (q i) (q k)*(u-l)^2 := by
  have h := coefficient_two_contacts_lens_width hg hjet i k j hl hu hx
    heql hequ hcross hix hky
  nlinarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
