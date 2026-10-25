/-
Adapted from: here:o093
Own proofs by session x0318, branch ae1ecd4; scalar chart interfaces by
session x0364 in the same LOT tree. The source module is
Submission/Obl/k4_scalar_critical_path_terminal/ConcreteProfiles.lean.
-/

import Submission.Obl.k4_scalar_linear_critical_extremizers.ConcreteRates

set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_linear_critical_extremizers.Split

open Set Filter
open scoped Topology

noncomputable section

theorem exists_caps_tendsto (dstar : ℝ) (hstar : dstar < 1) :
    ∃ caps err : ℕ → ℝ, (∀ i, caps i ∈ Ioo dstar 1) ∧
      Tendsto caps atTop (𝓝 dstar) ∧ (∀ i, 0 < err i) ∧ Tendsto err atTop (𝓝 0) := by
  let err := fun i : ℕ => 1 / ((i : ℝ) + 1)
  let caps := fun i => dstar + (1 - dstar) / 2 * err i
  have herrlim : Tendsto err atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have herr (i : ℕ) : 0 < err i := by dsimp [err]; positivity
  have herr₁ (i : ℕ) : err i ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (i : ℝ) + 1)).2
    have := Nat.cast_nonneg (α := ℝ) i
    linarith
  refine ⟨caps, err, ?_, ?_, herr, herrlim⟩
  · intro i
    have hfactor : 0 < (1 - dstar) / 2 := by linarith
    have hlo := mul_pos hfactor (herr i)
    have hhi := mul_le_mul_of_nonneg_left (herr₁ i) hfactor.le
    dsimp [caps]
    constructor <;> nlinarith
  · simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (x := dstar)).add (herrlim.const_mul ((1 - dstar) / 2))

/-- Actual unit-length maximizing exact problems have uniformly linear
relative profiles, in the fixed original angular class. -/
theorem class_maximizing_profiles (hinit : Initial) (hcalc : WeakCalculus) (hext : Extension)
    (S₀ η : ℝ) (hS : 0 < S₀) (hη : 0 < η)
    (hne : (badDimensions (AngularClass S₀ η) d Horizon).Nonempty) :
    ∃ p : ℕ → Code,
      (∀ i, AngularClass S₀ η (p i) ∧ L (p i) = 1 ∧ 0 < Horizon (p i)) ∧
      Tendsto (fun i => d (p i)) atTop (𝓝 (classDimension S₀ η)) ∧
      Tendsto (fun i => Horizon (p i)) atTop (𝓝 (classCriticalRate S₀ η)) ∧
      Tendsto (fun i => classRate S₀ η (d (p i))) atTop (𝓝 (classCriticalRate S₀ η)) ∧
      TendstoUniformlyOn (fun i r => f (p i) r - f (p i) 0)
        (fun r => classDimension S₀ η * r) atTop (Icc 0 1) := by
  let dstar := classDimension S₀ η
  let κ := classCriticalRate S₀ η
  have hstar₀ : 0 ≤ dstar := criticalDimension_nonneg _ _ _ hne
  have hstar₁ : dstar < 1 := criticalDimension_lt_one _ _ _ hne
  have hκ := class_critical_rate_bounds hinit hcalc hext S₀ η hS hη hne
  obtain ⟨caps, err, hcaps, hcapslim, herr, herrlim⟩ := exists_caps_tendsto dstar hstar₁
  obtain ⟨p, hp, hdimlim, hHlim, hRlim⟩ := exists_maximizing_sequence_along_caps
    (AngularClass S₀ η) d L Horizon (class_horizon_bound hinit S₀ η)
    (fun p hp => exact_dimension_bounds hp.1) hne
    (angularClass_unit_normalization hcalc S₀ η) caps err hcaps hcapslim herr herrlim
  have hcrit (q : Code) (hq : AngularClass S₀ η q) (hqH : 0 < Horizon q) : dstar ≤ d q :=
    criticalDimension_le_bad _ _ _ hq (exact_dimension_bounds hq.1).1
      (exact_dimension_bounds hq.1).2 hqH
  have hregular (i : ℕ) (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) :
      0 ≤ f (p i) s - f (p i) r ∧ f (p i) s - f (p i) r ≤ s - r :=
    exact_profile_regular (hp i).1.1 r s hr hrs (by simpa only [(hp i).2.1] using hs)
  have hdim (i : ℕ) : dstar ≤ d (p i) := hcrit _ (hp i).1 (hp i).2.2
  have hend (i : ℕ) : f (p i) 1 - f (p i) 0 ≤ d (p i) := by
    have ht := exact_terminal_cap (hp i).1.1 0 (by norm_num)
      (by simpa only [(hp i).2.1] using (zero_le_one : (0 : ℝ) ≤ 1))
    simpa only [(hp i).2.1, sub_zero, mul_one] using ht
  have hR₀ (i : ℕ) : 0 ≤ classRate S₀ η (d (p i)) := by
    have hb := horizon_le_extremalRate_mul _ _ _ _ (class_horizon_bound hinit S₀ η)
      (hp i).1 (le_rfl (a := d (p i)))
    rw [(hp i).2.1, mul_one] at hb
    exact (hp i).2.2.le.trans hb
  have hcoarse (i : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδstar : δ < dstar)
      (a r : ℝ) (ha : 0 < a) (har : a < r) (hr : r ≤ 1)
      (hcap : ∀ t ∈ Icc a r, f (p i) r - f (p i) t ≤ δ * (r - t)) :
      Horizon (p i) ≤ classRate S₀ η (d (p i)) * (1 - r) := by
    have hb := local_subcritical_original_horizon_bound hinit hcalc hext S₀ η dstar δ
      (classRate S₀ η (d (p i))) hS hη hcrit hδ.le hδstar (hδstar.trans hstar₁)
      (p i) (hp i).1
      (fun q hq hqd => horizon_le_extremalRate_mul _ _ _ _
        (class_horizon_bound hinit S₀ η) hq hqd)
      a r ha.le har (by simpa only [(hp i).2.1] using hr) hcap
    simpa only [(hp i).2.1] using hb
  refine ⟨p, hp, hdimlim, hHlim, hRlim, ?_⟩
  exact maximizing_profiles_uniformly_linear (fun i => f (p i)) (fun i => d (p i))
    (fun i => Horizon (p i)) (fun i => classRate S₀ η (d (p i))) dstar κ
    hstar₀ hstar₁.le hκ.1 hregular hdim hend hdimlim hHlim hRlim hR₀ hcoarse

/-- A bounded numerical error for a whole relative profile. -/
def profileError (p : Code) (dstar : ℝ) : ℝ :=
  sSup ((fun r => |f p r - f p 0 - dstar * r|) '' Icc 0 1)

theorem profileError_bounds {p : Code} (hp : Exact p) (hL : L p = 1)
    {dstar : ℝ} (hstar₀ : 0 ≤ dstar) (hstar₁ : dstar ≤ 1) :
    0 ≤ profileError p dstar ∧ ∀ r ∈ Icc 0 1,
      |f p r - f p 0 - dstar * r| ≤ profileError p dstar := by
  have hbdd : BddAbove ((fun r => |f p r - f p 0 - dstar * r|) '' Icc 0 1) := by
    refine ⟨1, ?_⟩
    rintro z ⟨r, hr, rfl⟩
    have hinc := exact_profile_regular hp 0 r (by norm_num) hr.1 (by simpa only [hL] using hr.2)
    have hmul : 0 ≤ dstar * r ∧ dstar * r ≤ 1 :=
      ⟨mul_nonneg hstar₀ hr.1, (mul_le_mul_of_nonneg_right hstar₁ hr.1).trans (by simpa using hr.2)⟩
    apply abs_le.mpr
    constructor <;> linarith [hr.2]
  have hzero : (0 : ℝ) ∈ ((fun r => |f p r - f p 0 - dstar * r|) '' Icc 0 1) :=
    ⟨0, by norm_num, by simp⟩
  exact ⟨le_csSup hbdd hzero, fun r hr => le_csSup hbdd ⟨r, hr, rfl⟩⟩

theorem profileError_tendsto_zero (p : ℕ → Code) (dstar : ℝ)
    (hp : ∀ i, Exact (p i)) (hL : ∀ i, L (p i) = 1)
    (hstar₀ : 0 ≤ dstar) (hstar₁ : dstar ≤ 1)
    (hlim : TendstoUniformlyOn (fun i r => f (p i) r - f (p i) 0)
      (fun r => dstar * r) atTop (Icc 0 1)) :
    Tendsto (fun i => profileError (p i) dstar) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun i => ha.trans_le
      (profileError_bounds (hp i) (hL i) hstar₀ hstar₁).1
  · intro b hb
    have hunif := Metric.tendstoUniformlyOn_iff.1 hlim (b / 2) (half_pos hb)
    filter_upwards [hunif] with i hi
    have hupper : profileError (p i) dstar ≤ b / 2 := by
      apply csSup_le
      · exact ⟨0, 0, by norm_num, by simp⟩
      · rintro z ⟨r, hr, rfl⟩
        have ht := hi r hr
        rw [Real.dist_eq, abs_sub_comm] at ht
        exact ht.le
    linarith

end

end Submission.Obl.k4_scalar_linear_critical_extremizers.Split
