import Submission.Obl.k4_finite_width_output_exclusion.RebaseTransfer
import Submission.Obl.k4_finite_width_output_exclusion.Scenarios

set_option maxRecDepth 4096

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

lemma choose_no_improvement (hc : Composition) (hi : Initial)
    {ds kr ell S η zeta Δ a e0 : ℝ} (hes : Extremal ds kr S η)
    (hell : 0 ≤ ell) (hunif : ∀ z : ℝ, 0 < z → UniformWidth ds kr S η (max 0 (ell - z)))
    (hzeta : 0 < zeta) (hΔ : 16 * zeta < Δ) (ha : 0 < a) (he0 : 0 < e0) :
    ∃ e t : ℝ, 0 < e ∧ e ≤ e0 ∧ 0 < t ∧
      ∀ p : Data, Valid p → p.L = 1 → p.S = S → p.η = η →
        p.d < ds + t → kr - t < Horizon p → ¬ Narrow p (kr + a) (ell + zeta) →
        NoImprovement p kr ell Δ zeta e := by
  rcases hes with ⟨hds, hds1, hkr, hkr1, hex, hupper, hlinear⟩
  have hΔpos : 0 < Δ := by linarith
  let gain : ℝ := kr * Δ / 2
  have hGainPos : 0 < gain := by dsimp [gain]; positivity
  obtain ⟨td, htd, hupper⟩ := hupper (gain / 4) (by positivity)
  obtain ⟨tw, htw, hwidth⟩ := hunif zeta hzeta (a / 4) (by positivity)
  let budget : ℝ := min gain (min a (min (tw * Δ) zeta))
  have hbudget : 0 < budget := by dsimp [budget]; positivity
  have hbg : budget ≤ gain := min_le_left _ _
  have hba : budget ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hbt : budget ≤ tw * Δ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbz : budget ≤ zeta :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let e : ℝ := min e0 (budget / (16 * (kr + ell + 2)))
  have he : 0 < e := by dsimp [e]; positivity
  have hee0 : e ≤ e0 := min_le_left _ _
  have heb : e ≤ budget / (16 * (kr + ell + 2)) := min_le_right _ _
  have hden : 0 < 16 * (kr + ell + 2) := by positivity
  have heb' : e * (16 * (kr + ell + 2)) ≤ budget := (le_div_iff₀ hden).1 heb
  have hegain : (kr + 1) * e ≤ gain / 16 := by
    linarith only [heb', hbg, mul_nonneg hell he.le, he.le]
  have hea : (kr + 1) * e ≤ a / 16 := by
    linarith only [heb', hba, mul_nonneg hell he.le, he.le]
  have het : (kr + 1) * e ≤ tw * Δ / 16 := by
    linarith only [heb', hbt, mul_nonneg hell he.le, he.le]
  have hez : ell * e ≤ zeta / 16 := by
    linarith only [heb', hbz, mul_nonneg hkr.le he.le, he.le]
  let t : ℝ := min td (min tw (min (gain / 16) (tw * Δ / 16)))
  have ht : 0 < t := by dsimp [t]; positivity
  have httd : t ≤ td := min_le_left _ _
  have httw : t ≤ tw := (min_le_right _ _).trans (min_le_left _ _)
  have htgin : t ≤ gain / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have httΔ : t ≤ tw * Δ / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨e, t, he, hee0, ht, ?_⟩
  intro p hp hpL hpS hpη hpd hpH hpbad
  constructor
  · intro r h w hr hrΔ hgain hknown
    obtain ⟨q, hq, hqL, hqd, hqS, hqη, hcost, hnarrow⟩ :=
      hc p hp r h w hr (by rw [hpL]; linarith) hknown
    have hcomp : Horizon p ≤ h + Horizon q := horizon_composition_le hi hp hq hcost
    have hdq : q.d < ds + td := by rw [hqd]; linarith
    have hqbound := hupper q hq (hqS.trans hpS) (hqη.trans hpη) hdq
    have hlen : q.L = 1 - r := by simpa only [hpL] using hqL
    have hlen1 : q.L ≤ 1 := by linarith
    have hrate : (gain / 4) * q.L ≤ gain / 4 :=
      mul_le_of_le_one_right (by positivity) hlen1
    rw [hlen] at hqbound hrate
    change h ≤ kr * r - gain + (kr + 1) * e at hgain
    linarith only [hcomp, hqbound, hrate, hpH, hgain, hegain, htgin, hGainPos]
  · intro r s hr hrΔ hrs hknown
    let h : ℝ := kr * s + e
    let w : ℝ := ell * s + Δ - 4 * zeta
    obtain ⟨q, hq, hqL, hqd, hqS, hqη, hcost, hnarrow⟩ :=
      hc p hp r h w hr (by rw [hpL]; linarith) hknown
    have hcomp : Horizon p ≤ h + Horizon q := horizon_composition_le hi hp hq hcost
    have hlen : q.L = 1 - r := by simpa only [hpL] using hqL
    have hlenΔ : Δ ≤ q.L := by linarith
    have hlen1 : q.L ≤ 1 := by linarith
    obtain ⟨u, hu, huL, hud, huS, huη, hnorm, hnormN⟩ := unit_normalization hi hq
    have hnear : kr - tw < Horizon u := by
      have htwlen : tw * Δ ≤ tw * q.L := mul_le_mul_of_nonneg_left hlenΔ htw.le
      have hs : s - r ≤ e := by linarith [(abs_le.1 hrs).1]
      have hkrs : kr * (s - r) ≤ kr * e := mul_le_mul_of_nonneg_left hs hkr.le
      apply (mul_lt_mul_iff_right₀ hq.length_pos).1
      dsimp [h] at hcomp
      rw [hlen] at hnorm htwlen ⊢
      have hpos : 0 < tw * Δ := mul_pos htw hΔpos
      linarith only [hpH, hcomp, hnorm, hkrs, httΔ, het, htwlen, hpos]
    have hdu : u.d < ds + tw := by rw [hud, hqd]; linarith
    have hn := hwidth u hu huL (huS.trans (hqS.trans hpS))
      (huη.trans (hqη.trans hpη)) hdu hnear
    have hwide := hnarrow _ _ (hnormN _ _ hn)
    apply hpbad
    apply narrow_mono hp (hn := hwide)
    · dsimp [h]
      have hs : s - r ≤ e := by linarith [(abs_le.1 hrs).1]
      have hkrs : kr * (s - r) ≤ kr * e := mul_le_mul_of_nonneg_left hs hkr.le
      have hsmall : q.L * (a / 4) ≤ a / 4 := mul_le_of_le_one_left (by positivity) hlen1
      rw [hlen] at hsmall ⊢
      linarith only [hkrs, hsmall, hea, ha]
    · dsimp [w]
      have hw0 : ell - zeta ≤ max 0 (ell - zeta) := le_max_right _ _
      have hmult := mul_le_mul_of_nonneg_left hw0 hq.length_pos.le
      have hzlen : zeta * q.L ≤ zeta := mul_le_of_le_one_right hzeta.le hlen1
      have hrs' : r - s ≤ e := (abs_le.1 hrs).2
      have hellrs : ell * (r - s) ≤ ell * e := mul_le_mul_of_nonneg_left hrs' hell
      rw [hlen] at hmult hzlen ⊢
      linarith only [hmult, hzlen, hellrs, hez, hΔ, hzeta]

end
end Submission.Obl.k4_finite_width_output_exclusion
