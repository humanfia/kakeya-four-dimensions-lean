import Submission.Obl.k4_raw_critical_segment_forests.EndpointSystems
import Submission.Obl.k4_raw_critical_segment_forests.CoarsenedEndpoints
import Submission.Obl.k4_finite_width_output_exclusion.RebaseTransfer

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The first positive target can be any endpoint in the unit interval. -/
theorem prefix_one (hc : Composition) (hi : Initial) {ds kr S η w : ℝ}
    (hes : Extremal ds kr S η) (hunif : UniformWidth ds kr S η w)
    {s : ℕ → ℝ} (hs : 0 < s 0) (hs1 : s 0 ≤ 1)
    {ε q : ℝ} (hε : 0 < ε) (hq : 0 < q) :
    ∃ t : ℝ, 0 < t ∧ ∀ p : Data, Valid p → p.L = 1 → p.S = S → p.η = η →
      p.d < ds + t → kr - t < Horizon p →
      ∃ (r : ℕ → ℝ) (M D : ℕ),
        (∀ i, i < 1 → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ s i ∧
          (s i = 1 → r i = 1)) ∧
        ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop, RawAt p kr w ε q σ 1 s r M D k := by
  have hkr : 0 < kr := hes.2.2.1
  have hkr1 : kr ≤ 1 := hes.2.2.2.1
  obtain ⟨tw, htw, hwidth⟩ := hunif (ε / 8) (by positivity)
  let e := min (ε / 8) (s 0 / 2)
  let b := min (ε / 8) (tw * s 0 / 8)
  have he : 0 < e := by dsimp [e]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have heε : e ≤ ε / 8 := min_le_left _ _
  have hes0 : e ≤ s 0 / 2 := min_le_right _ _
  have hbε : b ≤ ε / 8 := min_le_left _ _
  have hbtw : b ≤ tw * s 0 / 8 := min_le_right _ _
  obtain ⟨t, ht, hcoarse⟩ := capped_near_coarsening hc hi hes hs hs1 he hb htw
  refine ⟨t, ht, ?_⟩
  intro p hp hpL hpS hpη hpd hpH
  obtain ⟨r, d, G, hr, hrs, hrse, hfinal, hd, hout, hHout⟩ :=
    hcoarse p hp hpL hpS hpη hpd hpH
  let out : Data := {p with L := r, d := d, G := G}
  have hr1 : r ≤ 1 := hrs.trans hs1
  have hdist := (abs_le.mp hrse).1
  have hrlo : s 0 / 2 ≤ r := by linarith
  obtain ⟨u, hu, huL, hud, huS, huη, hnorm, hnormN⟩ := unit_normalization hi hout
  have hnear : kr - tw < Horizon u := by
    have hgap : b < tw * r := by nlinarith [mul_pos htw hs]
    have hscaled : r * (kr - tw) < r * Horizon u := by
      change Horizon out ≤ r * Horizon u at hnorm
      change kr * r - b < Horizon out at hHout
      nlinarith
    exact (mul_lt_mul_iff_right₀ hr).mp hscaled
  have hnu := hwidth u hu huL (huS.trans hpS) (huη.trans hpη)
    (by rw [hud]; exact hd) hnear
  have hno := hnormN (kr + ε / 8) w hnu
  have hlo : kr * s 0 - ε < Horizon out := by
    have hprod : kr * (s 0 - r) ≤ s 0 - r :=
      mul_le_of_le_one_left (by linarith) hkr1
    change kr * r - b < Horizon out at hHout
    nlinarith
  have hhi : r * (kr + ε / 8) < kr * s 0 + ε := by
    have hm := mul_le_mul_of_nonneg_left hrs hkr.le
    have heps := mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ ε / 8)
    nlinarith
  obtain ⟨M, D, hsystems⟩ := endpoint_systems hout hlo hhi hq hno
  refine ⟨fun _ => r, M, D, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    exact ⟨hrse.trans (by linarith), hr, hrs, hfinal⟩
  · intro σ hσ
    apply (hsystems σ hσ).mono
    rintro k ⟨κ, a, width, hκ, hK, hκN, ha, hTlo, hThi, hTM, hw⟩
    refine ⟨oneLayerForest (fromEndpoint a) κ, width, hκN,
      oneLayerForest_core_depth hκ hK (fromEndpoint_trueDepth ha), ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      exact ⟨hTlo, hThi, hTM⟩
    · intro z
      refine ⟨(hw z).1, (hw z).2.1, ?_, ?_⟩
      · intro _
        simpa only [mul_comm r w] using (hw z).2.2
      · intro hz
        exact False.elim (Nat.not_lt_zero _ hz)

end
end Submission.Obl.k4_raw_critical_segment_forests
