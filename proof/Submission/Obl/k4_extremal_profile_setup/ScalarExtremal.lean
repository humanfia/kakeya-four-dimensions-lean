import Mathlib

/-!
The two scalar optimizations in Section 4 of the supplied paper.  The index of
the family represents a length-one exact problem.  The only input beyond the
elementary horizon bounds is the uniform amplification furnished by terminal
extension followed by chart normalization.
-/

namespace Submission.Obl.k4_extremal_profile_setup

open Set

/-- Dimensions and relative horizons of a family of length-one problems. -/
structure RateFamily (α : Type*) where
  dim : α → ℝ
  rate : α → ℝ
  dim_pos : ∀ p, 0 < dim p
  dim_lt_one : ∀ p, dim p < 1
  rate_nonneg : ∀ p, 0 ≤ rate p
  rate_le_one : ∀ p, rate p ≤ 1

namespace RateFamily

variable {α : Type*} (F : RateFamily α)

/-- Uniform recovery of a positive relative horizon without increasing the cap. -/
def Amplifies : Prop :=
  ∀ d₀ : ℝ, d₀ < 1 → ∃ c : ℝ, 0 < c ∧
    ∀ p, F.dim p ≤ d₀ → 0 < F.rate p →
      ∃ q, F.dim q ≤ F.dim p ∧ c ≤ F.rate q

def badDimensions : Set ℝ := {d | ∃ p, F.dim p = d ∧ 0 < F.rate p}

noncomputable def criticalDimension : ℝ := sInf F.badDimensions

def rates (D : ℝ) : Set ℝ := {r | ∃ p, F.dim p < D ∧ F.rate p = r}

noncomputable def upperRate (D : ℝ) : ℝ := sSup (F.rates D)

theorem badDimensions_bddBelow : BddBelow F.badDimensions := by
  refine ⟨0, ?_⟩
  rintro d ⟨p, rfl, _⟩
  exact (F.dim_pos p).le

theorem rates_bddAbove (D : ℝ) : BddAbove (F.rates D) := by
  refine ⟨1, ?_⟩
  rintro r ⟨p, _, rfl⟩
  exact F.rate_le_one p

theorem criticalDimension_le {p : α} (hp : 0 < F.rate p) :
    F.criticalDimension ≤ F.dim p :=
  csInf_le F.badDimensions_bddBelow ⟨p, rfl, hp⟩

theorem criticalDimension_nonneg (hbad : ∃ p, 0 < F.rate p) :
    0 ≤ F.criticalDimension := by
  apply le_csInf
  · obtain ⟨p, hp⟩ := hbad
    exact ⟨F.dim p, p, rfl, hp⟩
  · rintro d ⟨p, rfl, _⟩
    exact (F.dim_pos p).le

theorem criticalDimension_lt_one (hbad : ∃ p, 0 < F.rate p) :
    F.criticalDimension < 1 := by
  obtain ⟨p, hp⟩ := hbad
  exact (F.criticalDimension_le hp).trans_lt (F.dim_lt_one p)

theorem exists_bad_below (hbad : ∃ p, 0 < F.rate p) {D : ℝ}
    (hD : F.criticalDimension < D) :
    ∃ p, F.dim p < D ∧ 0 < F.rate p := by
  have hn : F.badDimensions.Nonempty := by
    obtain ⟨p, hp⟩ := hbad
    exact ⟨F.dim p, p, rfl, hp⟩
  obtain ⟨d, ⟨p, rfl, hp⟩, hd⟩ := exists_lt_of_csInf_lt hn hD
  exact ⟨p, hd, hp⟩

theorem rate_eq_zero_below_critical {p : α} (hp : F.dim p < F.criticalDimension) :
    F.rate p = 0 := by
  apply le_antisymm _ (F.rate_nonneg p)
  by_contra hn
  exact (not_lt_of_ge (F.criticalDimension_le (lt_of_not_ge hn))) hp

theorem rates_nonempty (hbad : ∃ p, 0 < F.rate p) {D : ℝ}
    (hD : F.criticalDimension < D) : (F.rates D).Nonempty := by
  obtain ⟨p, hp, _⟩ := F.exists_bad_below hbad hD
  exact ⟨F.rate p, p, hp, rfl⟩

theorem rate_le_upperRate {D : ℝ} {p : α} (hp : F.dim p < D) :
    F.rate p ≤ F.upperRate D :=
  le_csSup (F.rates_bddAbove D) ⟨p, hp, rfl⟩

theorem upperRate_le_one (hbad : ∃ p, 0 < F.rate p) {D : ℝ}
    (hD : F.criticalDimension < D) : F.upperRate D ≤ 1 := by
  apply csSup_le (F.rates_nonempty hbad hD)
  rintro r ⟨p, _, rfl⟩
  exact F.rate_le_one p

/-- Amplification makes the lower bound uniform as the cap approaches its infimum. -/
theorem exists_uniform_positive_rate (hbad : ∃ p, 0 < F.rate p)
    (hamp : F.Amplifies) :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℝ, F.criticalDimension < D → c ≤ F.upperRate D := by
  let d₀ := (F.criticalDimension + 1) / 2
  have hd₀ : F.criticalDimension < d₀ := by
    dsimp [d₀]
    linarith [F.criticalDimension_lt_one hbad]
  have hd₀1 : d₀ < 1 := by
    dsimp [d₀]
    linarith [F.criticalDimension_lt_one hbad]
  obtain ⟨c, hc, hamp⟩ := hamp d₀ hd₀1
  refine ⟨c, hc, fun D hD => ?_⟩
  obtain ⟨p, hp, hpr⟩ :=
    F.exists_bad_below hbad (lt_min hD hd₀)
  obtain ⟨q, hqd, hqr⟩ := hamp p (lt_of_lt_of_le hp (min_le_right _ _)).le hpr
  exact hqr.trans (F.rate_le_upperRate (hqd.trans_lt (hp.trans_le (min_le_left _ _))))

/-- The critical rate is the right limit of the suprema of nearby relative horizons. -/
noncomputable def criticalRate : ℝ :=
  sInf {r | ∃ D : ℝ, F.criticalDimension < D ∧ F.upperRate D = r}

/-- The extremal selection, including its nearby uniform upper bound and the
vanishing assertion strictly below the critical dimension. -/
theorem exists_critical_rates (hbad : ∃ p, 0 < F.rate p) (hamp : F.Amplifies) :
    ∃ ds kr : ℝ, 0 ≤ ds ∧ ds < 1 ∧ 0 < kr ∧ kr ≤ 1 ∧
      (∀ t : ℝ, 0 < t → ∃ p, F.dim p < ds + t ∧ kr - t < F.rate p) ∧
      (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧
        ∀ p, F.dim p < ds + a → F.rate p ≤ kr + t) ∧
      (∀ p, F.dim p < ds → F.rate p = 0) := by
  classical
  obtain ⟨c, hc, hcu⟩ := F.exists_uniform_positive_rate hbad hamp
  let S : Set ℝ := {r | ∃ D : ℝ, F.criticalDimension < D ∧ F.upperRate D = r}
  have hSn : S.Nonempty :=
    ⟨F.upperRate (F.criticalDimension + 1), F.criticalDimension + 1, by linarith, rfl⟩
  have hSb : BddBelow S := by
    refine ⟨c, ?_⟩
    rintro r ⟨D, hD, rfl⟩
    exact hcu D hD
  have hkr : c ≤ F.criticalRate := by
    apply le_csInf hSn
    rintro r ⟨D, hD, rfl⟩
    exact hcu D hD
  have hkrU {D : ℝ} (hD : F.criticalDimension < D) :
      F.criticalRate ≤ F.upperRate D :=
    csInf_le hSb ⟨D, hD, rfl⟩
  refine ⟨F.criticalDimension, F.criticalRate, F.criticalDimension_nonneg hbad,
    F.criticalDimension_lt_one hbad, hc.trans_le hkr,
    (hkrU (by linarith : F.criticalDimension < F.criticalDimension + 1)).trans
      (F.upperRate_le_one hbad (by linarith)), ?_, ?_, ?_⟩
  · intro t ht
    have hD : F.criticalDimension < F.criticalDimension + t := by linarith
    have hlt : F.criticalRate - t < F.upperRate (F.criticalDimension + t) := by
      linarith [hkrU hD]
    obtain ⟨r, ⟨p, hp, rfl⟩, hr⟩ :=
      exists_lt_of_lt_csSup (F.rates_nonempty hbad hD) hlt
    exact ⟨p, hp, hr⟩
  · intro t ht
    obtain ⟨r, ⟨D, hD, rfl⟩, hr⟩ :=
      exists_lt_of_csInf_lt hSn (show F.criticalRate < F.criticalRate + t by linarith)
    refine ⟨D - F.criticalDimension, sub_pos.mpr hD, fun p hp => ?_⟩
    apply le_trans (F.rate_le_upperRate (show F.dim p < D by linarith)) hr.le
  · exact fun p hp => F.rate_eq_zero_below_critical hp

/-- A subcritical secant gives a coarsened problem with zero horizon.  Composition
then bounds the original cost by the cost of the remaining interval.  The
quantitative location of the endpoint comes from minimizing the tilted profile.
-/
def SecantReduction (f : α → ℝ → ℝ) : Prop :=
  ∀ p (a b q : ℝ), 0 ≤ a → a < b → b ≤ 1 → 0 < q → q < 1 →
    f p b - f p a < q * (b - a) →
    (∀ p', F.dim p' ≤ q → F.rate p' = 0) →
    ∀ U : ℝ, 0 ≤ U → (∀ p', F.dim p' ≤ F.dim p → F.rate p' ≤ U) →
      ∃ r : ℝ, a < r ∧ r ≤ b ∧
        q * (b - a) - (f p b - f p a) ≤ q * (r - a) ∧
        F.rate p ≤ U * (1 - r)

/-- A quantitative form of the relative-profile part of Proposition 4.3.
Only relative values of the profiles occur.  A fixed error produces a secant
deficit, hence a definite loss of horizon, contradicting near-maximality.
-/
theorem uniform_relative_profiles (f : α → ℝ → ℝ)
    (hinc : ∀ p (r s : ℝ), 0 ≤ r → r ≤ s → s ≤ 1 →
      0 ≤ f p s - f p r ∧ f p s - f p r ≤ s - r)
    (hcap : ∀ p (r : ℝ), 0 ≤ r → r ≤ 1 →
      f p 1 - f p r ≤ F.dim p * (1 - r))
    (hred : F.SecantReduction f) {ds kr : ℝ}
    (hds : 0 ≤ ds) (hds1 : ds < 1) (hkr : 0 < kr)
    (hupper : ∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧
      ∀ p, F.dim p < ds + a → F.rate p ≤ kr + t)
    (hzero : ∀ p, F.dim p < ds → F.rate p = 0) :
    ∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧
      ∀ p, F.dim p < ds + a → kr - a < F.rate p →
        ∀ r : ℝ, 0 ≤ r → r ≤ 1 → |f p r - f p 0 - ds * r| ≤ t := by
  intro t ht
  let θ := min t 1
  have hθ : 0 < θ := lt_min ht zero_lt_one
  have hθt : θ ≤ t := min_le_left _ _
  by_cases hds0 : ds = 0
  · refine ⟨θ, hθ, fun p hp _ r hr hr1 => ?_⟩
    have h₁ := (hinc p 0 r le_rfl hr hr1).1
    have h₂ := (hinc p r 1 hr hr1 le_rfl).1
    have h₃ := hcap p 0 le_rfl zero_le_one
    rw [hds0, zero_add] at hp
    rw [hds0, zero_mul, sub_zero]
    rw [abs_of_nonneg h₁]
    nlinarith
  have hdspos : 0 < ds := lt_of_le_of_ne hds (Ne.symm hds0)
  let q := ds - min (ds / 2) (θ / 8)
  have hq : 0 < q := by
    have := min_le_left (ds / 2) (θ / 8)
    dsimp [q]
    linarith
  have hqds : q < ds := by
    have : 0 < min (ds / 2) (θ / 8) := lt_min (by positivity) (by positivity)
    dsimp [q]
    linarith
  have hq1 : q < 1 := hqds.trans hds1
  have hgap : ds - q ≤ θ / 8 := by
    have := min_le_right (ds / 2) (θ / 8)
    dsimp [q]
    linarith
  let u := kr * θ / 16
  have hu : 0 < u := by dsimp [u]; positivity
  obtain ⟨a₀, ha₀, hU⟩ := hupper u hu
  let a := min (a₀ / 2) (min (θ / 8) u)
  have ha : 0 < a := lt_min (by positivity) (lt_min (by positivity) hu)
  have haa₀ : a ≤ a₀ := (min_le_left _ _).trans (by linarith)
  have haθ : a ≤ θ / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hau : a ≤ u := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨a, ha, fun p hp hnear r hr hr1 => ?_⟩
  have hbound : ∀ p', F.dim p' ≤ F.dim p → F.rate p' ≤ kr + u := by
    intro p' hp'
    exact hU p' (hp'.trans_lt (hp.trans_le (by linarith)))
  have hsub : ∀ p', F.dim p' ≤ q → F.rate p' = 0 :=
    fun p' hp' => hzero p' (hp'.trans_lt hqds)
  have exclude (a' b' : ℝ) (ha' : 0 ≤ a') (hab : a' < b') (hb' : b' ≤ 1)
      (hdef : θ / 2 < q * (b' - a') - (f p b' - f p a')) : False := by
    have hsec : f p b' - f p a' < q * (b' - a') := by linarith
    obtain ⟨s, has, hsb, hloc, hcost⟩ :=
      hred p a' b' q ha' hab hb' hq hq1 hsec hsub (kr + u) (by positivity) hbound
    have hs : 0 ≤ s := ha'.trans has.le
    have hqs : q * (s - a') ≤ s := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq1.le) (sub_nonneg.mpr has.le)]
    have hlarge : θ / 2 < s := hdef.trans_le (hloc.trans hqs)
    have hdrop : F.rate p ≤ kr + u - kr * (θ / 2) := by
      have hmul := mul_le_mul_of_nonneg_left hlarge.le hkr.le
      have hmul' := mul_nonneg hu.le hs
      nlinarith
    dsimp [u] at hdrop hau
    nlinarith [mul_pos hkr hθ]
  apply le_trans (b := θ) _ hθt
  apply abs_le.mpr
  constructor
  · by_contra hn
    have herr : f p r - f p 0 - ds * r < -θ := lt_of_not_ge hn
    have hrpos : 0 < r := by
      by_contra hnp
      have heq : r = 0 := le_antisymm (le_of_not_gt hnp) hr
      rw [heq] at herr
      simp only [mul_zero, sub_self] at herr
      linarith
    apply exclude 0 r le_rfl hrpos hr1
    have hgr : (ds - q) * r ≤ θ / 8 := by
      calc
        (ds - q) * r ≤ (ds - q) * 1 :=
          mul_le_mul_of_nonneg_left hr1 (sub_nonneg.mpr hqds.le)
        _ ≤ θ / 8 := by simpa using hgap
    nlinarith
  · by_contra hn
    have herr : θ < f p r - f p 0 - ds * r := lt_of_not_ge hn
    have htotal := hcap p 0 le_rfl zero_le_one
    have hrlt : r < 1 := by
      by_contra hnr
      have heq : r = 1 := le_antisymm hr1 (le_of_not_gt hnr)
      rw [heq] at herr
      nlinarith
    apply exclude r 1 hr hrlt le_rfl
    have hgr : (ds - q) * (1 - r) ≤ θ / 8 := by
      calc
        (ds - q) * (1 - r) ≤ (ds - q) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hqds.le)
        _ ≤ θ / 8 := by simpa using hgap
    nlinarith

/-- Both optimizations and the linear relative-profile conclusion, in length-one
units.  Geometric normalization and composition enter only through the two
explicit inputs `Amplifies` and `SecantReduction`.
-/
theorem exists_critical_profile (f : α → ℝ → ℝ)
    (hinc : ∀ p (r s : ℝ), 0 ≤ r → r ≤ s → s ≤ 1 →
      0 ≤ f p s - f p r ∧ f p s - f p r ≤ s - r)
    (hcap : ∀ p (r : ℝ), 0 ≤ r → r ≤ 1 →
      f p 1 - f p r ≤ F.dim p * (1 - r))
    (hbad : ∃ p, 0 < F.rate p) (hamp : F.Amplifies)
    (hred : F.SecantReduction f) :
    ∃ ds kr : ℝ, 0 ≤ ds ∧ ds < 1 ∧ 0 < kr ∧ kr ≤ 1 ∧
      (∀ t : ℝ, 0 < t → ∃ p, F.dim p < ds + t ∧ kr - t < F.rate p) ∧
      (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧
        ∀ p, F.dim p < ds + a → F.rate p ≤ kr + t) ∧
      (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧
        ∀ p, F.dim p < ds + a → kr - a < F.rate p →
          ∀ r : ℝ, 0 ≤ r → r ≤ 1 → |f p r - f p 0 - ds * r| ≤ t) := by
  obtain ⟨ds, kr, hds, hds1, hkr, hkr1, hnear, hupper, hzero⟩ :=
    F.exists_critical_rates hbad hamp
  exact ⟨ds, kr, hds, hds1, hkr, hkr1, hnear, hupper,
    F.uniform_relative_profiles f hinc hcap hred hds hds1 hkr hupper hzero⟩

end RateFamily

end Submission.Obl.k4_extremal_profile_setup
