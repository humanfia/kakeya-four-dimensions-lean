-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_transverse_pair_moment.Sublevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_transverse_pair_moment

open MeasureTheory Set

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

end WangZahlLot.Obl.wz_jet_transverse_pair_moment
