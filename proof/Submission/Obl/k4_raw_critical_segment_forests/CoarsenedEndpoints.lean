import Submission.Obl.k4_raw_critical_segment_forests.CappedDepth
import Submission.Obl.k4_raw_critical_segment_forests.CoarsenedHorizon

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- A capped coarsening at any requested positive endpoint stays near maximal.
Its depth accuracy, density-cap neighborhood, and horizon error are independent
requested parameters. The terminal target is attained exactly. -/
theorem capped_near_coarsening (hc : Composition) (hi : Initial)
    {ds kr S η s e b z : ℝ} (hes : Extremal ds kr S η)
    (hs : 0 < s) (hs1 : s ≤ 1) (he : 0 < e) (hb : 0 < b) (hz : 0 < z) :
    ∃ t : ℝ, 0 < t ∧ ∀ p : Data, Valid p → p.L = 1 → p.S = S → p.η = η →
      p.d < ds + t → kr - t < Horizon p →
      ∃ (r d : ℝ), ∃ G, 0 < r ∧ r ≤ s ∧ |r - s| ≤ e ∧ (s = 1 → r = 1) ∧
        d < ds + z ∧ Valid {p with L := r, d := d, G := G} ∧
        kr * r - b < Horizon {p with L := r, d := d, G := G} := by
  rcases hes with ⟨hds, hds1, hkr, hkr1, hex, hupper, hlinear⟩
  let tilt : ℝ := min z (1 - ds) / 4
  have htilt : 0 < tilt := by dsimp [tilt]; positivity
  have htiltz : tilt < z := by
    have := min_le_left z (1 - ds)
    dsimp [tilt]
    linarith
  have htilt1 : ds + tilt < 1 := by
    have := min_le_right z (1 - ds)
    dsimp [tilt]
    linarith
  let ep : ℝ := min e (s / 2)
  have hep : 0 < ep := by dsimp [ep]; positivity
  have hepe : ep ≤ e := min_le_left _ _
  have heps : ep < s := (min_le_right _ _).trans_lt (by linarith)
  let u : ℝ := b / 8
  have hu : 0 < u := by dsimp [u]; positivity
  obtain ⟨td, htd, hupper⟩ := hupper u hu
  obtain ⟨tl, htl, hlinear⟩ := hlinear (tilt * ep / 4) (by positivity)
  let t := min td (min tl (min tilt u))
  have ht : 0 < t := by dsimp [t]; positivity
  have httd : t ≤ td := min_le_left _ _
  have httl : t ≤ tl := (min_le_right _ _).trans (min_le_left _ _)
  have httilt : t ≤ tilt :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htu : t ≤ u :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨t, ht, ?_⟩
  intro p hp hpL hpS hpη hpd hpH
  have hreg : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ p.L →
      0 ≤ p.f y - p.f x ∧ p.f y - p.f x ≤ y - x := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hprofile : ∀ x : ℝ, 0 ≤ x → x ≤ p.L →
      |p.f x - p.f 0 - ds * x| ≤ tilt * ep / 4 := by
    have hl := hlinear p hp hpS hpη (by linarith : p.d < ds + tl)
      (by rw [hpL]; linarith : (kr - tl) * p.L < Horizon p)
    intro x hx hxL
    simpa only [hpL, mul_one] using hl x hx hxL
  have hchoose : ∃ r : ℝ, 0 < r ∧ r ≤ s ∧ |r - s| ≤ e ∧ (s = 1 → r = 1) ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ r → p.f r - p.f x ≤ (ds + tilt) * (r - x) := by
    by_cases hs_eq : s = 1
    · have hcap : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
          p.f 1 - p.f x ≤ (ds + tilt) * (1 - x) := by
        intro x hx hx1
        have h := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 x hx (by rwa [hpL])
        rw [hpL] at h
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
      refine ⟨1, zero_lt_one, by rw [hs_eq], ?_, fun _ => rfl, hcap⟩
      simpa only [hs_eq, sub_self, abs_zero] using he.le
    · obtain ⟨r, hr, hrs, hrse, hcap⟩ := capped_depth_near hreg htilt hep heps
        (by rw [hpL]; exact hs1) hprofile
      exact ⟨r, hr, hrs, hrse.trans hepe, fun h => False.elim (hs_eq h), hcap⟩
  obtain ⟨r, hr, hrs, hrse, hfinal, hcap⟩ := hchoose
  have hrL : r ≤ p.L := by rw [hpL]; exact hrs.trans hs1
  obtain ⟨G, hout⟩ := valid_coarsened hp hr hrL (by linarith : 0 < ds + tilt) htilt1 hcap
  let out : Data := {p with L := r, d := ds + tilt, G := G}
  have hbound : Horizon p ≤ Horizon out + (kr + u) * (p.L - r) := by
    apply horizon_coarsened_lower_le hc hi hp hr.le hrL hout
    intro q hq hqd hqS hqη
    apply hupper q hq (hqS.trans hpS) (hqη.trans hpη)
    rw [hqd]
    linarith
  have hrem : 1 - r ≤ 1 := by linarith
  have humul : u * (1 - r) ≤ u := mul_le_of_le_one_right hu.le hrem
  refine ⟨r, ds + tilt, G, hr, hrs, hrse, hfinal, by linarith, hout, ?_⟩
  rw [hpL] at hbound
  dsimp [u] at htu humul hbound
  linarith

end
end Submission.Obl.k4_raw_critical_segment_forests
