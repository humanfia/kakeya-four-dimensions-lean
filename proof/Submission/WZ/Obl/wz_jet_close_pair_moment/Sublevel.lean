-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_close_pair_moment.Sublevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_close_pair_moment

open MeasureTheory Set

/-- Three zeros force a zero of the second derivative between the outer two. -/
theorem exists_deriv2_eq_zero_of_three_zeros {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {x y z : ℝ} (hxy : x < y) (hyz : y < z)
    (hx : f x = 0) (hy : f y = 0) (hz : f z = 0) :
    ∃ t ∈ Ioo x z, deriv (deriv f) t = 0 := by
  obtain ⟨u, hu, hdu⟩ := exists_deriv_eq_zero hxy hf.continuous.continuousOn (hx.trans hy.symm)
  obtain ⟨v, hv, hdv⟩ := exists_deriv_eq_zero hyz hf.continuous.continuousOn (hy.trans hz.symm)
  obtain ⟨t, ht, hdt⟩ := exists_deriv_eq_zero (hu.2.trans hv.1)
    (hf.deriv' (n := 1)).continuous.continuousOn (hdu.trans hdv.symm)
  exact ⟨t, ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩, hdt⟩

private theorem deriv2_sub_quadratic {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (D u v w x y z t : ℝ) :
    deriv (deriv (fun s => D * f s -
      (u * (s-y)*(s-z) + v*(s-x)*(s-z) + w*(s-x)*(s-y)))) t =
      D * deriv (deriv f) t - 2*(u+v+w) := by
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hddf : Differentiable ℝ (deriv f) :=
    (hf.deriv' (n := 1)).differentiable (by norm_num)
  have first : deriv (fun s => D * f s -
      (u * (s-y)*(s-z) + v*(s-x)*(s-z) + w*(s-x)*(s-y))) =
      fun s => D * deriv f s -
        (u * (2*s-y-z) + v*(2*s-x-z) + w*(2*s-x-y)) := by
    funext s
    simp (disch := fun_prop) only [deriv_fun_sub, deriv_fun_add, deriv_fun_mul,
      deriv_id'', deriv_const, mul_one, sub_zero]
    ring
  rw [first]
  simp (disch := fun_prop) only [deriv_fun_sub, deriv_fun_add, deriv_fun_mul,
    deriv_const_mul_id, deriv_const, sub_zero]
  ring

/-- Quantitative divided differences: three small values and a lower curvature
bound limit the product of the two adjacent gaps. -/
theorem sublevel_three_point {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {x y z A c : ℝ} (hxy : x < y) (hyz : y < z)
    (hx : |f x| ≤ A) (hy : |f y| ≤ A) (hz : |f z| ≤ A)
    (hcurv : ∀ t ∈ Ioo x z, c ≤ |deriv (deriv f) t|) :
    c * (y-x) * (z-y) ≤ 4*A := by
  let D := (y-x)*(z-y)*(z-x)
  let u := f x * (z-y)
  let v := -(f y * (z-x))
  let w := f z * (y-x)
  let H : ℝ → ℝ := fun t => D * f t -
    (u * (t-y)*(t-z) + v*(t-x)*(t-z) + w*(t-x)*(t-y))
  have hH : ContDiff ℝ 2 H := by dsimp [H]; fun_prop
  have hHx : H x = 0 := by dsimp [H, D, u, v, w]; ring
  have hHy : H y = 0 := by dsimp [H, D, u, v, w]; ring
  have hHz : H z = 0 := by dsimp [H, D, u, v, w]; ring
  obtain ⟨t, ht, hdt⟩ := exists_deriv2_eq_zero_of_three_zeros hH hxy hyz hHx hHy hHz
  change deriv (deriv (fun s => D * f s -
    (u*(s-y)*(s-z) + v*(s-x)*(s-z) + w*(s-x)*(s-y)))) t = 0 at hdt
  rw [deriv2_sub_quadratic hf] at hdt
  have hD : 0 < D := mul_pos (mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hyz))
    (sub_pos.mpr (hxy.trans hyz))
  have he : D * |deriv (deriv f) t| = 2 * |u+v+w| := by
    have he := congrArg abs (sub_eq_zero.mp hdt)
    simpa only [abs_mul, abs_of_pos hD, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using he
  have hQ : |u+v+w| ≤ 2*A*(z-x) := by
    calc
      |u+v+w| ≤ |u| + |v| + |w| :=
        (abs_add_le (u+v) w).trans (add_le_add (abs_add_le u v) le_rfl)
      _ = |f x| * (z-y) + |f y| * (z-x) + |f z| * (y-x) := by
        simp only [u, v, w, abs_mul, abs_neg, abs_of_pos (sub_pos.mpr hxy),
          abs_of_pos (sub_pos.mpr hyz), abs_of_pos (sub_pos.mpr (hxy.trans hyz))]
      _ ≤ A*(z-y) + A*(z-x) + A*(y-x) := by gcongr; linarith
      _ = 2*A*(z-x) := by ring
  have hbound : D*c ≤ 4*A*(z-x) := by
    have h := mul_le_mul_of_nonneg_left (hcurv t ht) hD.le
    nlinarith
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr (hxy.trans hyz))).mp
  calc
    (z-x)*(c*(y-x)*(z-y)) = D*c := by dsimp [D]; ring
    _ ≤ 4*A*(z-x) := hbound
    _ = (z-x)*(4*A) := by ring

/-- A compact set without three points separated by more than `L` has length
at most `2 L`. The two covering intervals begin and end at its extrema. -/
theorem volume_le_two_mul_of_no_three {S : Set ℝ} (hS : IsCompact S) {L : ℝ}
    (hL : 0 ≤ L)
    (hthree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, L < y-x → L < z-y → False) :
    volume S ≤ ENNReal.ofReal (2*L) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨x, hx, hxmin⟩ := hS.exists_isLeast hne
  obtain ⟨z, hz, hzmax⟩ := hS.exists_isGreatest hne
  have hsub : S ⊆ Icc x (x+L) ∪ Icc (z-L) z := by
    intro y hy
    by_cases hleft : y ≤ x+L
    · exact Or.inl ⟨hxmin hy, hleft⟩
    by_cases hright : z-L ≤ y
    · exact Or.inr ⟨hright, hzmax hy⟩
    exact (hthree x hx y hy z hz (by linarith) (by linarith)).elim
  calc
    volume S ≤ volume (Icc x (x+L) ∪ Icc (z-L) z) := measure_mono hsub
    _ ≤ volume (Icc x (x+L)) + volume (Icc (z-L) z) := measure_union_le _ _
    _ = ENNReal.ofReal (2*L) := by
      rw [Real.volume_Icc, Real.volume_Icc]
      have h1 : x+L-x = L := by ring
      have h2 : z-(z-L) = L := by ring
      rw [h1, h2, ← ENNReal.ofReal_add hL hL]
      congr 1
      ring

/-- A lower bound on the first derivative controls the diameter of a sublevel set. -/
theorem sublevel_dist_le_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {a b A c x y : ℝ} (hc : 0 < c)
    (hderiv : ∀ t ∈ Icc a b, c ≤ |deriv f t|)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hfx : |f x| ≤ A) (hfy : |f y| ≤ A) :
    dist x y ≤ 2*A/c := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hfx
  have hordered : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
      |f u| ≤ A → |f v| ≤ A → u < v → v-u ≤ 2*A/c := by
    intro u hu v hv hfu hfv huv
    obtain ⟨t, ht, hdt⟩ := exists_deriv_eq_slope f huv hf.continuous.continuousOn
      hf.differentiableOn
    have ht' : t ∈ Icc a b := ⟨hu.1.trans ht.1.le, ht.2.le.trans hv.2⟩
    have he := congrArg abs ((eq_div_iff (sub_ne_zero.mpr huv.ne')).mp hdt)
    rw [abs_mul, abs_of_pos (sub_pos.mpr huv)] at he
    have hval : |f v-f u| ≤ 2*A := by
      calc
        |f v-f u| ≤ |f v|+|f u| := abs_sub _ _
        _ ≤ A+A := add_le_add hfv hfu
        _ = 2*A := by ring
    apply (le_div_iff₀ hc).mpr
    calc
      (v-u)*c ≤ (v-u)*|deriv f t| := by gcongr; exact hderiv t ht'
      _ = |f v-f u| := by nlinarith [he]
      _ ≤ 2*A := hval
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy.le)]
    nlinarith [hordered x hx y hy hfx hfy hxy]
  · simpa only [dist_self] using div_nonneg (mul_nonneg (by norm_num) hA) hc.le
  · rw [dist_comm, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hyx.le)]
    nlinarith [hordered y hy x hx hfy hfx hyx]

/-- The one-dimensional first-derivative sublevel estimate. -/
theorem volume_sublevel_le_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {a b A c : ℝ} (hc : 0 < c)
    (hderiv : ∀ t ∈ Icc a b, c ≤ |deriv f t|) :
    volume {t | t ∈ Icc a b ∧ |f t| ≤ A} ≤ ENNReal.ofReal (2*A/c) := by
  apply (Real.volume_le_diam _).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  exact sublevel_dist_le_of_deriv hf hc hderiv hx.1 hy.1 hx.2 hy.2

/-- The one-dimensional second-derivative sublevel estimate. -/
theorem volume_sublevel_le_of_deriv2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hcurv : ∀ t ∈ Icc a b, c ≤ |deriv (deriv f) t|) :
    volume {t | t ∈ Icc a b ∧ |f t| ≤ A} ≤
      ENNReal.ofReal (4 * Real.sqrt (A/c)) := by
  let S := {t | t ∈ Icc a b ∧ |f t| ≤ A}
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_le hf.continuous.abs continuous_const)
  have hroot : (Real.sqrt (A/c))^2 = A/c := Real.sq_sqrt (div_nonneg hA hc.le)
  have hscale : c * (2*Real.sqrt (A/c))^2 = 4*A := by
    rw [mul_pow, hroot]
    field_simp
    ring
  have hbound := volume_le_two_mul_of_no_three hS
    (by positivity : 0 ≤ 2*Real.sqrt (A/c)) (by
      intro x hx y hy z hz hxy hyz
      have hxy0 : x < y := by linarith [Real.sqrt_nonneg (A/c)]
      have hyz0 : y < z := by linarith [Real.sqrt_nonneg (A/c)]
      have hsmall := sublevel_three_point hf hxy0 hyz0 hx.2 hy.2 hz.2 (by
        intro t ht
        apply hcurv t
        exact ⟨hx.1.1.trans ht.1.le, ht.2.le.trans hz.1.2⟩)
      have hprod : (2*Real.sqrt (A/c))^2 < (y-x)*(z-y) := by
        rw [pow_two]
        exact (mul_le_mul_of_nonneg_left hyz.le (by positivity)).trans_lt
          (mul_lt_mul_of_pos_right hxy (sub_pos.mpr hyz0))
      have hstrict := mul_lt_mul_of_pos_left hprod hc
      nlinarith)
  convert hbound using 1
  congr 1
  ring

end WangZahlLot.Obl.wz_jet_close_pair_moment
