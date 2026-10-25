import Submission.Obl.k4_extremal_profile_setup.Horizon
import Submission.Obl.k4_extremal_profile_setup.ScalarExtremal

/-! Apply the scalar optimizations to the exact frozen problem predicates.
All lengths remain competitors in the family; length normalization is needed
only when producing the final length-one near-maximizers.
-/

namespace Submission.Obl.k4_extremal_profile_setup

theorem Data.Valid.d_pos {p : Data} (hp : p.Valid) : 0 < p.d := hp.2.2.2.2.1

theorem Data.Valid.d_lt_one {p : Data} (hp : p.Valid) : p.d < 1 := hp.2.2.2.2.2.1

theorem Data.Valid.profile {p : Data} (hp : p.Valid) :
    ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ p.L →
      0 ≤ p.f s - p.f r ∧ p.f s - p.f r ≤ s - r := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, hinc, _⟩
  exact hinc

theorem Data.Valid.cap {p : Data} (hp : p.Valid) :
    ∀ r : ℝ, 0 ≤ r → r ≤ p.L → p.f p.L - p.f r ≤ p.d * (p.L - r) := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcap, _⟩
  exact hcap

/-- Exact problems with the fixed angular parameters of the optimization. -/
def ValidData (S η : ℝ) := {p : Data // p.Valid ∧ p.S = S ∧ p.η = η}

/-- The scalar family includes every positive length.  Depths and horizons are
expressed in the individual problem's own length units. -/
noncomputable def rateFamily (hi : InitialHorizon) (S η : ℝ) : RateFamily (ValidData S η) where
  dim p := p.1.d
  rate p := horizon p.1 / p.1.L
  dim_pos p := p.2.1.d_pos
  dim_lt_one p := p.2.1.d_lt_one
  rate_nonneg p := div_nonneg (horizon_nonneg hi p.2.1) p.2.1.L_pos.le
  rate_le_one p := (div_le_one p.2.1.L_pos).mpr (horizon_le_length hi p.2.1)

noncomputable def relativeProfile {S η : ℝ} (p : ValidData S η) (r : ℝ) : ℝ :=
  p.1.f (p.1.L * r) / p.1.L

theorem relativeProfile_increment {S η : ℝ} (p : ValidData S η)
    (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) :
    0 ≤ relativeProfile p s - relativeProfile p r ∧
      relativeProfile p s - relativeProfile p r ≤ s - r := by
  have hL := p.2.1.L_pos
  have h := p.2.1.profile (p.1.L * r) (p.1.L * s)
    (mul_nonneg hL.le hr) (mul_le_mul_of_nonneg_left hrs hL.le)
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hL.le)
  dsimp [relativeProfile]
  rw [← sub_div]
  exact ⟨div_nonneg h.1 hL.le, (div_le_iff₀ hL).mpr (by nlinarith [h.2])⟩

theorem relativeProfile_cap (hi : InitialHorizon) {S η : ℝ} (p : ValidData S η)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    relativeProfile p 1 - relativeProfile p r ≤ (rateFamily hi S η).dim p * (1 - r) := by
  have hL := p.2.1.L_pos
  have h := p.2.1.cap (p.1.L * r) (mul_nonneg hL.le hr)
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1 hL.le)
  dsimp [relativeProfile, rateFamily]
  rw [mul_one, ← sub_div]
  apply (div_le_iff₀ hL).mpr
  nlinarith

/-- Length normalization only needs to preserve a lower bound for the relative
horizon.  Taking a subsequence to enforce the new base bound is therefore allowed.
-/
def UnitNormalization : Prop :=
  ∀ S η : ℝ, ∀ p : ValidData S η,
    ∃ q : ValidData S η, q.1.L = 1 ∧ q.1.d ≤ p.1.d ∧
      horizon p.1 / p.1.L ≤ horizon q.1

/-- The extremal setup in terms of exact-problem records. -/
def ExtremalProfile (ds kr S η : ℝ) : Prop :=
  0 ≤ ds ∧ ds < 1 ∧ 0 < kr ∧ kr ≤ 1 ∧
  (∀ t : ℝ, 0 < t → ∃ p : ValidData S η,
    p.1.L = 1 ∧ p.1.d < ds + t ∧ kr - t < horizon p.1) ∧
  (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧
    ∀ p : ValidData S η, p.1.d < ds + a → horizon p.1 ≤ (kr + t) * p.1.L) ∧
  (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧
    ∀ p : ValidData S η, p.1.d < ds + a → (kr - a) * p.1.L < horizon p.1 →
      ∀ r : ℝ, 0 ≤ r → r ≤ p.1.L → |p.1.f r - p.1.f 0 - ds * r| ≤ t * p.1.L)

/-- The concrete theorem is reduced to length normalization and the two geometric
cost properties.  This statement retains the exact fixed-format horizon infimum.
-/
theorem extremalProfile_of_geometry (hi : InitialHorizon) (hnorm : UnitNormalization)
    {S η : ℝ} (hamp : (rateFamily hi S η).Amplifies)
    (hred : (rateFamily hi S η).SecantReduction relativeProfile)
    (hbad : ∃ p : ValidData S η, 0 < horizon p.1) :
    ∃ ds kr : ℝ, ExtremalProfile ds kr S η := by
  have hbad' : ∃ p, 0 < (rateFamily hi S η).rate p := by
    obtain ⟨p, hp⟩ := hbad
    exact ⟨p, div_pos hp p.2.1.L_pos⟩
  obtain ⟨ds, kr, hds, hds1, hkr, hkr1, hnear, hupper, hlinear⟩ :=
    (rateFamily hi S η).exists_critical_profile relativeProfile relativeProfile_increment
      (relativeProfile_cap hi) hbad' hamp hred
  refine ⟨ds, kr, hds, hds1, hkr, hkr1, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨p, hpd, hpr⟩ := hnear t ht
    obtain ⟨q, hqL, hqd, hqr⟩ := hnorm S η p
    exact ⟨q, hqL, hqd.trans_lt hpd, hpr.trans_le hqr⟩
  · intro t ht
    obtain ⟨a, ha, hupper⟩ := hupper t ht
    refine ⟨a, ha, fun p hp => ?_⟩
    exact (div_le_iff₀ p.2.1.L_pos).mp (hupper p hp)
  · intro t ht
    obtain ⟨a, ha, hlinear⟩ := hlinear t ht
    refine ⟨a, ha, fun p hp hH r hr hrL => ?_⟩
    have hHr : kr - a < (rateFamily hi S η).rate p :=
      (lt_div_iff₀ p.2.1.L_pos).mpr hH
    have hrl : r / p.1.L ≤ 1 := (div_le_one p.2.1.L_pos).mpr hrL
    have hlin := hlinear p hp hHr (r / p.1.L) (div_nonneg hr p.2.1.L_pos.le) hrl
    dsimp [relativeProfile] at hlin
    rw [mul_div_cancel₀ r p.2.1.L_pos.ne', mul_zero] at hlin
    have heq : p.1.f r / p.1.L - p.1.f 0 / p.1.L - ds * (r / p.1.L) =
        (p.1.f r - p.1.f 0 - ds * r) / p.1.L := by ring
    rw [heq, abs_div, abs_of_pos p.2.1.L_pos] at hlin
    exact (div_le_iff₀ p.2.1.L_pos).mp hlin

end Submission.Obl.k4_extremal_profile_setup
