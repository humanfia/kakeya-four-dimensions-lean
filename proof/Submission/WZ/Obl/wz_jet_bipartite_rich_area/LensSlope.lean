-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.LensSlope.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LensWidth
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.StationaryContact

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- Rolle's theorem controls every slope between two equal endpoint values
by the upper curvature bound times the interval length. -/
theorem abs_deriv_le_curvature_mul_width {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {l u x M : ℝ} (hlu : l < u) (hx : x ∈ Icc l u) (heq : f l = f u)
    (hcurv : ∀ t ∈ Icc l u, |deriv (deriv f) t| ≤ M) :
    |deriv f x| ≤ M*(u-l) := by
  obtain ⟨z, hz, hzero⟩ := exists_deriv_eq_zero hlu hf.continuous.continuousOn heq
  have hd : Differentiable ℝ (deriv f) :=
    (hf.deriv' (n := 1)).differentiable (by norm_num)
  have hbound := (convex_Icc l u).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => hd t)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hcurv t ht) hx ⟨hz.1.le, hz.2.le⟩
  simp only [Real.norm_eq_abs, hzero, zero_sub, abs_neg, abs_sub_comm z x] at hbound
  have hdist : |x-z| ≤ u-l := abs_le.mpr ⟨by linarith [hx.1, hz.2], by linarith [hx.2, hz.1]⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hcurv x hx)
  exact hbound.trans (mul_le_mul_of_nonneg_left hdist hM)

/-- Positive curvature controls the distance between two times by the
absolute difference of their slopes. -/
theorem curvature_mul_dist_le_slope_dist {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {x y c : ℝ} (hcurv : ∀ t ∈ uIcc x y, c ≤ deriv (deriv f) t) :
    c*|x-y| ≤ |deriv f x-deriv f y| := by
  rcases le_total x y with hxy | hyx
  · have h := curvature_slope_gap hf (left_mem_uIcc (a := x) (b := y))
      (right_mem_uIcc (a := x) (b := y)) hxy hcurv
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    nlinarith [neg_le_abs (deriv f x-deriv f y)]
  · have h := curvature_slope_gap hf (right_mem_uIcc (a := x) (b := y))
      (left_mem_uIcc (a := x) (b := y)) hyx hcurv
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    nlinarith [le_abs_self (deriv f x-deriv f y)]

/-- Two slope contacts to a common lower-curvature curve have close times
if the first time is inside a lens between the upper curves. The gain is
linear in the ratio of within-color to cross-color curvature bounds. -/
theorem two_slope_contacts_lens_width {f g b : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hb : ContDiff ℝ 2 b)
    {l u x y c M η : ℝ} (hlu : l < u) (hx : x ∈ Icc l u)
    (hl : f l = g l) (hu : f u = g u)
    (hcurv : ∀ t ∈ Icc l u, |deriv (deriv f) t - deriv (deriv g) t| ≤ M)
    (hcross : ∀ t ∈ uIcc x y, c ≤ deriv (deriv g) t - deriv (deriv b) t)
    (hfx : |deriv f x-deriv b x| ≤ η) (hgy : |deriv g y-deriv b y| ≤ η) :
    c*|x-y| ≤ M*(u-l)+2*η := by
  have hwidth := abs_deriv_le_curvature_mul_width (f := f-g) (M := M)
    (hf.sub hg) hlu hx (by simp only [Pi.sub_apply, hl, hu, sub_self])
    (by simpa only [deriv2_sub_of_contDiff_two hf hg, Pi.sub_apply] using hcurv)
  have hdist := curvature_mul_dist_le_slope_dist (f := g-b) (c := c) (x := x) (y := y)
    (hg.sub hb)
    (by simpa only [deriv2_sub_of_contDiff_two hg hb, Pi.sub_apply] using hcross)
  simp only [deriv_sub_of_contDiff_two hf hg, deriv_sub_of_contDiff_two hg hb,
    Pi.sub_apply] at hwidth hdist
  have htriangle := abs_add_le (deriv g x-deriv f x)
    ((deriv f x-deriv b x)-(deriv g y-deriv b y))
  have htriangle' := abs_sub (deriv f x-deriv b x) (deriv g y-deriv b y)
  have heq : (deriv g x-deriv f x)+
      ((deriv f x-deriv b x)-(deriv g y-deriv b y)) =
      (deriv g x-deriv b x)-(deriv g y-deriv b y) := by ring
  rw [heq, abs_sub_comm (deriv g x) (deriv f x)] at htriangle
  linarith

/-- Coefficient form of the linear lens-width estimate. No smallness
hypothesis on the value error is needed, because only slope contacts enter. -/
theorem coefficient_slope_contacts_lens_width {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i k j : Fin n) {l u x y D η : ℝ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hlu : l < u) (hx : x ∈ Icc l u)
    (heql : g i l = g k l) (hequ : g i u = g k u)
    (hcross : ∀ t ∈ uIcc x y,
      D/120 ≤ deriv (deriv (g k)) t - deriv (deriv (g j)) t)
    (hix : |deriv (g i) x-deriv (g j) x| ≤ η)
    (hky : |deriv (g k) y-deriv (g j) y| ≤ η) :
    D*|x-y| ≤ 2280*dist (q i) (q k)*(u-l)+240*η := by
  have h := two_slope_contacts_lens_width (hg i) (hg k) (hg j) hlu hx heql hequ
    (fun t ht => (deriv2_le_jetDistance (g i) (g k) t).trans
      (hjet i k t ⟨hl.trans ht.1, ht.2.trans hu⟩).2) hcross hix hky
  nlinarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
