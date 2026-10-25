/- Adapted from this LOT tree, o105, sessions x0351 and x0367,
Submission/Obl/k4_critical_path_framework/Profile.lean at origin/split/s042. -/
import Submission.Obl.k4_extremal_profile_setup.ScalarBridge
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ProfileCompactness

/-! Profile minimization in the construction of critical paths (Proposition 4.3). -/

namespace Submission.Obl.k4_extremal_profile_setup

open Set

/-- Monotone unit-speed increments on the depth interval. -/
def ProfileIncrement (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r

/-- Reuse the accepted profile extension theorem to obtain continuity on the interval. -/
theorem ProfileIncrement.continuousOn {f : ℝ → ℝ} {L : ℝ}
    (hf : ProfileIncrement f L) : ContinuousOn f (Icc 0 L) := by
  obtain ⟨g, hg, heq, _⟩ :=
    Submission.Obl.k4_native_grid_profile_extension.Profiles.extend_profile_from_grid
      (s := Icc 0 L) (fun r => f r) (fun r s hrs => hf r s r.property.1 hrs s.property.2)
  exact hg.continuous.continuousOn.congr (fun r hr => (heq ⟨r, hr⟩).symm)

/-- A tilted-profile minimizer supplies the endpoint slope cap on its left. -/
theorem tilted_minimizer {f : ℝ → ℝ} {L a b q : ℝ}
    (hf : ProfileIncrement f L) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
    ∃ r ∈ Icc a b, ∀ x ∈ Icc a r, f r - f x ≤ q * (r - x) := by
  have hcont : ContinuousOn (fun x => f x - q * x) (Icc a b) :=
    (hf.continuousOn.mono (Icc_subset_Icc ha hb)).sub
      (continuous_const.mul continuous_id).continuousOn
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcont
  refine ⟨r, hr, fun x hx => ?_⟩
  have h := hmin ⟨hx.1, hx.2.trans hr.2⟩
  dsimp at h
  nlinarith

/-- The strict secant comparison keeps the minimizer away from the left endpoint. -/
theorem tilted_minimizer_interior {f : ℝ → ℝ} {L a b q : ℝ}
    (hf : ProfileIncrement f L) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ L)
    (hsec : f b - f a < q * (b - a)) :
    ∃ r ∈ Ioc a b, ∀ x ∈ Icc a r, f r - f x ≤ q * (r - x) := by
  have hcont : ContinuousOn (fun x => f x - q * x) (Icc a b) :=
    (hf.continuousOn.mono (Icc_subset_Icc ha hb)).sub
      (continuous_const.mul continuous_id).continuousOn
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hcont
  have hne : r ≠ a := by
    intro heq
    have h := hmin (right_mem_Icc.mpr hab.le)
    dsimp at h
    rw [heq] at h
    nlinarith
  refine ⟨r, ⟨lt_of_le_of_ne hr.1 hne.symm, hr.2⟩, fun x hx => ?_⟩
  have h := hmin ⟨hx.1, hx.2.trans hr.2⟩
  dsimp at h
  nlinarith

/-- A nearly linear profile forces a minimizer of a steeper tilt near the right endpoint. -/
theorem tilted_minimizer_near_endpoint {f : ℝ → ℝ} {r t d ε err : ℝ}
    (hε : 0 < ε)
    (ht : |f t - f 0 - d * t| ≤ err) (hr : |f r - f 0 - d * r| ≤ err)
    (hmin : f t - (d + ε) * t ≤ f r - (d + ε) * r) :
    r - 2 * err / ε ≤ t := by
  have ht' := (abs_le.mp ht).1
  have hr' := (abs_le.mp hr).2
  have h : r - t ≤ 2 * err / ε := (le_div_iff₀ hε).mpr (by nlinarith)
  linarith

/-- A local terminal cap below one extends to a global terminal cap below one.
The unit Lipschitz bound controls the portion to the left of the local interval. -/
theorem global_terminal_cap_of_local {f : ℝ → ℝ} {L a r q : ℝ}
    (hf : ProfileIncrement f L) (ha : 0 ≤ a) (har : a < r) (hrL : r ≤ L)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hcap : ∀ x ∈ Icc a r, f r - f x ≤ q * (r - x)) :
    ∃ d : ℝ, q ≤ d ∧ 0 ≤ d ∧ d < 1 ∧
      ∀ x ∈ Icc 0 r, f r - f x ≤ d * (r - x) := by
  have hr : 0 < r := ha.trans_lt har
  let d : ℝ := (q * (r - a) + a) / r
  have hdq : q ≤ d := by
    apply (le_div_iff₀ hr).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1.le) ha]
  have hd1 : d < 1 := by
    apply (div_lt_one hr).mpr
    nlinarith [mul_pos (sub_pos.mpr hq1) (sub_pos.mpr har)]
  have hdr : d * r = q * (r - a) + a := div_mul_cancel₀ _ hr.ne'
  refine ⟨d, hdq, hq.trans hdq, hd1, fun x hx => ?_⟩
  by_cases hax : a ≤ x
  · exact (hcap x ⟨hax, hx.2⟩).trans
      (mul_le_mul_of_nonneg_right hdq (sub_nonneg.mpr hx.2))
  · have hxa : x ≤ a := (lt_of_not_ge hax).le
    have hleft := (hf x a hx.1 hxa (har.le.trans hrL)).2
    have hright := hcap a ⟨le_rfl, har.le⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hd1.le) hx.1]

end Submission.Obl.k4_extremal_profile_setup
