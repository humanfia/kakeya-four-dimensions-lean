import Submission.Obl.k4_raw_critical_segment_forests.Extend
import Submission.Obl.k4_raw_critical_segment_forests.PrefixOne
import Submission.Obl.k4_raw_critical_segment_forests.PrefixInterface
import Submission.Obl.k4_raw_critical_segment_forests.Wrapper

set_option maxHeartbeats 2000000

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Backward selection of the prefix precision permits a new segment of any
positive target length, independently of the requested width error. -/
theorem prefix_construction (hnorm : NestedNormalizationPrepared) : PrefixConstruction := by
  intro hprep hc hi ds kr S η w hes hw hunif m
  induction m with
  | zero =>
    intro s hm
    omega
  | succ m ih =>
    intro s hm hs hstep ε q hε hε1 hq
    by_cases hm0 : m = 0
    · subst m
      exact prefix_one hc hi hes hunif (hs 0 (by omega)).1 (hs 0 (by omega)).2 hε hq
    have hmpos : 0 < m := by omega
    have hkr : 0 ≤ kr := hes.2.2.1.le
    have hkr1 : kr ≤ 1 := hes.2.2.2.1
    have hgap : 0 < s m - s (m - 1) := by
      have hstep' := hstep (m - 1) (by omega)
      have hm' : m - 1 + 1 = m := by omega
      rw [hm'] at hstep'
      linarith
    obtain ⟨tw, htw, hunarrow⟩ := hunif (ε / 8) (by positivity)
    let ε₀ := min (ε / 16) (tw * (s m - s (m - 1)) / 128)
    have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
    have hε₀ε : ε₀ ≤ ε / 16 := min_le_left _ _
    have hε₀gap : ε₀ ≤ tw * (s m - s (m - 1)) / 128 := min_le_right _ _
    have hε₀1 : ε₀ ≤ 1 := by linarith
    obtain ⟨tp, htp, hprefix⟩ := ih s hmpos
      (fun i hi => hs i (by omega)) (fun i hi => hstep i (by omega)) ε₀ q hε₀ hε₀1 hq
    let e := min (ε / 16) ((s m - s (m - 1)) / 4)
    let b := min (ε / 16) (tw * (s m - s (m - 1)) / 128)
    have he : 0 < e := by dsimp [e]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    have heε : e ≤ ε / 16 := min_le_left _ _
    have hegap : e ≤ (s m - s (m - 1)) / 4 := min_le_right _ _
    have hbε : b ≤ ε / 16 := min_le_left _ _
    have hbgap : b ≤ tw * (s m - s (m - 1)) / 128 := min_le_right _ _
    obtain ⟨tc, htc, hcoarse⟩ := capped_near_coarsening hc hi hes
      (hs m (by omega)).1 (hs m (by omega)).2 he hb htw
    let t := min tp tc
    have ht : 0 < t := by dsimp [t]; positivity
    have htp' : t ≤ tp := min_le_left _ _
    have htc' : t ≤ tc := min_le_right _ _
    refine ⟨t, ht, ?_⟩
    intro p hp hpL hpS hpη hpd hpH
    obtain ⟨r, Mp, Dp, hr, hfamily⟩ := hprefix p hp hpL hpS hpη
      (by linarith) (by linarith)
    obtain ⟨L, d, G, hL, hLs, hLdist, hLfinal, hd, hout, hHout⟩ :=
      hcoarse p hp hpL hpS hpη (by linarith) (by linarith)
    let rr : ℕ → ℝ := fun i => if i = m then L else r i
    have hrrm : rr m = L := if_pos rfl
    have hrreq (i : ℕ) (hi : i < m) : r i = rr i := by
      dsimp only [rr]
      rw [if_neg (by omega : i ≠ m)]
    have hrrprev : rr (m - 1) = r (m - 1) := (hrreq (m - 1) (by omega)).symm
    have hrprev := hr (m - 1) (by omega)
    have hLprev : rr (m - 1) < L := by
      rw [hrrprev]
      have := (abs_le.mp hLdist).1
      linarith [hrprev.2.2.1]
    have hspdist : s (m - 1) - rr (m - 1) ≤ ε₀ := by
      rw [hrrprev]
      have hdist := (abs_le.mp hrprev.1).1
      linarith only [hdist]
    have hbnear : b + 2 * ε₀ < tw * (L - rr (m - 1)) := by
      have hdist := (abs_le.mp hLdist).1
      have hg : 3 * (s m - s (m - 1)) / 4 ≤ L - rr (m - 1) := by
        rw [hrrprev]
        linarith only [hdist, hegap, hrprev.2.2.1]
      have hmul := mul_le_mul_of_nonneg_left hg htw.le
      nlinarith only [hmul, hbgap, hε₀gap, mul_pos htw hgap]
    have hHlo : kr * s m - ε < Horizon {p with L := L, d := d, G := G} := by
      have hdist := (abs_le.mp hLdist).1
      have hprod : kr * (s m - L) ≤ s m - L := mul_le_of_le_one_left
        (by linarith) hkr1
      nlinarith
    have hrfinal : ∀ i, i < m + 1 → |rr i - s i| ≤ ε ∧ 0 < rr i ∧ rr i ≤ s i ∧
        (s i = 1 → rr i = 1) := by
      intro i hi
      by_cases him : i = m
      · subst i
        rw [hrrm]
        exact ⟨hLdist.trans (by linarith), hL, hLs, hLfinal⟩
      · have hi' : i < m := by omega
        rw [← hrreq i hi']
        exact ⟨(hr i hi').1.trans (by linarith), (hr i hi').2⟩
    have hrvalid : ∀ i, i < m → 0 < rr i ∧ rr i ≤ p.L := by
      intro i hi
      have hri := hrfinal i (by omega)
      rw [hpL]
      exact ⟨hri.2.1, hri.2.2.1.trans (hs i (by omega)).2⟩
    have hfamily' : ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop, RawAt p kr w ε₀ q σ m s rr Mp Dp k := by
      intro σ hσ
      apply (hfamily σ hσ).mono
      rintro k ⟨a, v, ha⟩
      exact ⟨a, v, ha.congr_depth hmpos hrreq⟩
    obtain ⟨M, D, hMp, hDp, φ, a, v, lst, hφ, hcert⟩ :=
      prepared_raw_sequence hprep hp hmpos hrvalid hfamily'
    have hwidth : ∀ u : Data, Valid u → u.L = 1 → u.d = d → u.S = p.S → u.η = p.η →
        kr - tw < Horizon u → Narrow u (kr + ε / 8) w := by
      intro u hu huL hud huS huη huH
      apply hunarrow u hu huL (huS.trans hpS) (huη.trans hpη)
      · rw [hud]
        exact hd
      · exact huH
    obtain ⟨Mf, Df, hforests⟩ := extend_prepared hnorm hi hp hmpos hkr hkr1
      hε hε1 hε₀ (by linarith : ε₀ ≤ ε / 8) hq htw hrrm.symm
      (hLs.trans (hs m (by omega)).2) hLs (hs m (by omega)).2
      (by rw [hrrprev]; exact hrprev.2.1) hLprev
      (by rw [hrrprev]; exact hrprev.2.2.1) hspdist hbnear G hout hHout hHlo
      hwidth φ a v lst hφ (fun n => (hcert n).1) (fun n => (hcert n).2)
    exact ⟨rr, Mf, Df, hrfinal, hforests⟩

theorem statement_of_nested_normalization (hnorm : NestedNormalizationPrepared) : Statement :=
  statement_of_prefix (prefix_construction hnorm)

end
end Submission.Obl.k4_raw_critical_segment_forests
