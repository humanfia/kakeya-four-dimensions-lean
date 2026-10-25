/-
Adapted from: here:o093
Own proofs by session x0318, branch ae1ecd4; scalar chart interfaces by
session x0364 in the same LOT tree. The source module is
Submission/Obl/k4_scalar_critical_path_terminal/CriticalProfiles.lean.
-/

import Submission.Obl.k4_scalar_linear_critical_extremizers.Profile
import Submission.Obl.k4_scalar_linear_critical_extremizers.Horizon

/-!
Relative-profile linearity on maximizing sequences (the supplied paper,
Proposition `prop:critical-path`, first assertion). A quantitative secant
argument gives uniform convergence directly. The zero-cost consequence
of terminal extension at a locally subcritical endpoint is explicit.
-/

namespace Submission.Obl.k4_scalar_linear_critical_extremizers

open Set Filter
open scoped Topology

/-- A strict horizon gap at depth `a` rules out every subcritical secant
to its right. Minimize the tilted profile to turn a bad secant into a
coarsened endpoint at which the horizon would be too small. -/
theorem lower_secants_of_horizon_gap {f : ℝ → ℝ} {H K a δ : ℝ}
    (hf : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ 1 →
      0 ≤ f s - f r ∧ f s - f r ≤ s - r)
    (hK : 0 ≤ K) (ha : 0 < a)
    (hgap : K * (1 - a) < H)
    (hcoarse : ∀ x r : ℝ, 0 < x → x < r → r ≤ 1 →
      (∀ t ∈ Icc x r, f r - f t ≤ δ * (r - t)) → H ≤ K * (1 - r)) :
    ∀ x ∈ Icc a 1, ∀ y ∈ Icc x 1, δ * (y - x) ≤ f y - f x := by
  intro x hx y hy
  by_contra hlow
  have hxy : x < y := by
    rcases hy.1.eq_or_lt with h | h
    · subst y
      simp at hlow
    · exact h
  have hcont : ContinuousOn f (Icc x y) :=
    (profile_lipschitzOn hf).continuousOn.mono
      (fun _ ht => ⟨(ha.le.trans hx.1).trans ht.1, ht.2.trans hy.2⟩)
  obtain ⟨r, hr, hmin, hcap⟩ := exists_tilted_profile_minimum hxy.le hcont δ
  have hxr : x < r := by
    by_contra h
    have heq : r = x := le_antisymm (le_of_not_gt h) hr.1
    have hm := hmin y ⟨hxy.le, le_rfl⟩
    rw [heq] at hm
    have hlow' := lt_of_not_ge hlow
    nlinarith
  have hH := hcoarse x r (ha.trans_le hx.1) hxr (hr.2.trans hy.2) hcap
  have hK' : K * (1 - r) ≤ K * (1 - a) :=
    mul_le_mul_of_nonneg_left (by linarith [hx.1, hr.1]) hK
  exact (not_le_of_gt hgap) (hH.trans hK')

/-- Explicit uniform error bound from lower secants away from depth zero.
Only relative profile values enter this estimate. -/
theorem uniform_relative_profile_bound {f : ℝ → ℝ} {a δ dstar d : ℝ}
    (hf : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ 1 →
      0 ≤ f s - f r ∧ f s - f r ≤ s - r)
    (ha : a ∈ Icc 0 1) (hδ : 0 ≤ δ) (hδstar : δ ≤ dstar)
    (hstar₁ : dstar ≤ 1) (hstard : dstar ≤ d)
    (hend : f 1 - f 0 ≤ d)
    (hsec : ∀ x ∈ Icc a 1, ∀ y ∈ Icc x 1, δ * (y - x) ≤ f y - f x) :
    ∀ x ∈ Icc 0 1, |f x - f 0 - dstar * x| ≤ d - δ + a := by
  intro x hx
  have hstar₀ : 0 ≤ dstar := hδ.trans hδstar
  have hδd : δ ≤ d := hδstar.trans hstard
  have hxinc := hf 0 x (by norm_num) hx.1 hx.2
  apply abs_le.mpr
  by_cases hax : a ≤ x
  · have hpre := hsec a ⟨le_rfl, ha.2⟩ x ⟨hax, hx.2⟩
    have hsuf := hsec x ⟨hax, hx.2⟩ 1 ⟨hx.2, le_rfl⟩
    have hfa := (hf 0 a (by norm_num) ha.1 ha.2).1
    have hprod₁ : (dstar - δ) * x ≤ dstar - δ := by
      simpa using mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr hδstar)
    have hprod₂ : δ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right (hδstar.trans hstar₁) ha.1
    have hprod₀ : 0 ≤ (dstar - δ) * x :=
      mul_nonneg (sub_nonneg.mpr hδstar) hx.1
    constructor <;> nlinarith [ha.1]
  · have hxa : x ≤ a := le_of_not_ge hax
    have hprod : 0 ≤ dstar * x ∧ dstar * x ≤ x :=
      ⟨mul_nonneg hstar₀ hx.1, by simpa using mul_le_mul_of_nonneg_right hstar₁ hx.1⟩
    constructor <;> linarith

/-- A maximizing sequence has a uniformly linear relative profile once
terminal extension excludes positive horizon below the critical dimension.
No compactness or boundedness of `f i 0` is required. -/
theorem maximizing_profiles_uniformly_linear
    (f : ℕ → ℝ → ℝ) (d H K : ℕ → ℝ) (dstar k : ℝ)
    (hstar₀ : 0 ≤ dstar) (hstar₁ : dstar ≤ 1) (hk : 0 < k)
    (hf : ∀ i r s, 0 ≤ r → r ≤ s → s ≤ 1 →
      0 ≤ f i s - f i r ∧ f i s - f i r ≤ s - r)
    (hd : ∀ i, dstar ≤ d i)
    (hend : ∀ i, f i 1 - f i 0 ≤ d i)
    (hdlim : Tendsto d atTop (𝓝 dstar))
    (hHlim : Tendsto H atTop (𝓝 k))
    (hKlim : Tendsto K atTop (𝓝 k)) (hK : ∀ i, 0 ≤ K i)
    (hcoarse : ∀ (i : ℕ) (δ : ℝ), 0 < δ → δ < dstar →
      ∀ x r : ℝ, 0 < x → x < r → r ≤ 1 →
      (∀ t ∈ Icc x r, f i r - f i t ≤ δ * (r - t)) →
        H i ≤ K i * (1 - r)) :
    TendstoUniformlyOn (fun i x => f i x - f i 0) (fun x => dstar * x)
      atTop (Icc 0 1) := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  by_cases hstar : dstar = 0
  · have hdε : ∀ᶠ i in atTop, d i < ε :=
      hdlim.eventually_lt tendsto_const_nhds (by simpa [hstar] using hε)
    filter_upwards [hdε] with i hi x hx
    have hinc := hf i 0 x (by norm_num) hx.1 hx.2
    have hsuf := (hf i x 1 hx.1 hx.2 le_rfl).1
    have htotal := hend i
    rw [hstar, zero_mul, Real.dist_eq, abs_sub_comm, sub_zero,
      abs_of_nonneg hinc.1]
    linarith
  · have hstarpos : 0 < dstar := lt_of_le_of_ne hstar₀ (Ne.symm hstar)
    let a := min (ε / 4) (1 / 2)
    let η := min (dstar / 2) (ε / 4)
    let δ := dstar - η
    have ha₀ : 0 < a := lt_min (by positivity) (by norm_num)
    have haε : a ≤ ε / 4 := min_le_left _ _
    have ha₁ : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have hη : 0 < η := lt_min (half_pos hstarpos) (by positivity)
    have hηstar : η ≤ dstar / 2 := min_le_left _ _
    have hηε : η ≤ ε / 4 := min_le_right _ _
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hδstar : δ < dstar := by dsimp [δ]; linarith
    have hgap : ∀ᶠ i in atTop, K i * (1 - a) < H i :=
      (hKlim.mul_const (1 - a)).eventually_lt hHlim (by nlinarith)
    have hdε : ∀ᶠ i in atTop, d i < dstar + ε / 4 :=
      hdlim.eventually_lt tendsto_const_nhds (by linarith)
    filter_upwards [hgap, hdε] with i hi hdi x hx
    have hsec := lower_secants_of_horizon_gap (hf i) (hK i) ha₀ hi
      (hcoarse i δ hδ hδstar)
    have hbound := uniform_relative_profile_bound (hf i) ⟨ha₀.le, ha₁⟩ hδ.le
      hδstar.le hstar₁ (hd i) (hend i) hsec x hx
    rw [Real.dist_eq, abs_sub_comm]
    apply hbound.trans_lt
    dsimp [δ]
    linarith

end Submission.Obl.k4_scalar_linear_critical_extremizers
