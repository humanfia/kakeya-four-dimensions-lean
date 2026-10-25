/- Adapted from same-tree o119, session x0401, commit 19d6f4b3eda81f6d7228948a9996d889733ab672,
   Submission/Obl/k4_finite_width_critical_contradiction/Monotonicity.lean (namespace renamed; any
   earlier provenance is kept below). -/
/- Adapted from same-tree o105, session x0351, commit 735310f,
   Submission/Obl/k4_critical_path_framework/Monotonicity.lean. -/
import Submission.Obl.k4_finite_width_path_realization.Toolkit.Definitions
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat
import Submission.Obl.k4_native_grid_profile_extension.Dyadic

/-! Increasing format bounds and slack preserves the complete chart conditions. -/

namespace Submission.Obl.k4_finite_width_path_realization

open MeasureTheory

theorem Data.Valid.B_pos {p : Data} (hp : p.Valid) (k : ℕ) (γ : Fin (p.W k)) :
    0 < p.B k γ := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, htemp, _⟩
  obtain ⟨M, D, htemp⟩ := htemp
  exact ((htemp k).2.2.2.1 γ).2.1

/-- No geometric test or genuine floor is dropped when slack is enlarged. -/
theorem Chart.mono {Nk κ κ' j r Bv : ℝ} {M M' D D' T : ℕ}
    {Ev : Set Incidence} {c u : Spatial} {Q : Frame} {R : Test}
    {A : Set Trajectory} {F : Set Incidence} {ex ex' : Prop}
    (hNk : 1 ≤ Nk) (hM : M ≤ M') (hD : D ≤ D') (hκ0 : 0 < κ) (hκ : κ ≤ κ')
    (hB : 0 ≤ Bv) (hex : ex → ex')
    (hchart : Chart Nk M D κ T j r Bv Ev c u Q R A F ex) :
    Chart Nk M' D' κ' T j r Bv Ev c u Q R A F ex' := by
  obtain ⟨hdet, hcu, hQ, hsize, hdegree, hcoeff, hA, hF, hfmt, hline, hsel, hfloor⟩ := hchart
  have hpow : Nk ^ M ≤ Nk ^ M' := pow_le_pow_right₀ hNk hM
  have hδ : 0 < δ Nk r :=
    Submission.Obl.k4_native_grid_profile_extension.dyadicWidth_pos Nk r
  refine ⟨hdet, hcu.trans hpow, hQ.trans hpow, hsize.trans ?_, hdegree,
    fun e => (hcoeff e).trans hpow, hA, hF, ?_, ?_, ?_, hex hfloor⟩
  · exact div_le_div_of_nonneg_right hκ (by positivity)
  · intro i
    exact ⟨Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hfmt i).1 hpow hD,
      Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hfmt i).2 hpow hD⟩
  · intro l hl
    obtain ⟨hindex, hbound, htime⟩ := hline l hl
    refine ⟨hindex.trans hpow, fun e => (hbound e).trans hpow, fun t ht => ?_⟩
    obtain ⟨hnorm, hvalue, hder, hder2⟩ := htime t ht
    exact ⟨hnorm.trans hκ,
      hvalue.trans (mul_le_mul_of_nonneg_right hκ hδ.le),
      hder.trans (mul_le_mul_of_nonneg_right hκ hB),
      hder2.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hκ (sq_nonneg Bv)) hδ.le)⟩
  · intro p hp
    obtain ⟨hEv, hAp, htime, hder⟩ := hsel p hp
    exact ⟨hEv, hAp, htime, (div_le_div_of_nonneg_left hB hκ0 hκ).trans hder⟩

/-- Keep all chart data and enlarge only the allowed slack. -/
def Atlas.enlarge {p : Data} {k : ℕ} (a : Atlas p k) (κ' : ℝ) : Atlas p k :=
  {a with κ := κ'}

theorem Atlas.TrueAt.enlarge {p : Data} (hp : p.Valid) {k M D : ℕ}
    {a : Atlas p k} {κ' r : ℝ} (ha : a.TrueAt M D r) (hκ1 : 1 ≤ a.κ) (hκ : a.κ ≤ κ') :
    (a.enlarge κ').TrueAt M D r := by
  have hκ0 : 0 < a.κ := lt_of_lt_of_le zero_lt_one hκ1
  obtain ⟨hC, hdis, hchart, hmass⟩ := ha
  refine ⟨hC, hdis, fun b => ?_, ?_⟩
  · apply Chart.mono (le_trans (by norm_num) (hp.1 k)) le_rfl le_rfl hκ0 hκ
      (hp.B_pos k (a.γ b)).le _ (hchart b)
    intro hfloor
    apply le_trans (ENNReal.ofReal_le_ofReal _) hfloor
    apply div_le_div_of_nonneg_left (mul_nonneg (Real.rpow_nonneg (le_trans (by norm_num) (hp.1 k)) _) (abs_nonneg _))
      (mul_pos (by positivity) hκ0)
    exact mul_le_mul_of_nonneg_left hκ (by positivity)
  · apply le_trans (ENNReal.ofReal_le_ofReal _) hmass
    change κ'⁻¹ ≤ a.κ⁻¹
    simpa only [one_div] using one_div_le_one_div_of_le hκ0 hκ

/-- Add the original subpower slack to a true system obtained without that lower bound. -/
theorem terminalAt_of_weak {p : Data} (hp : p.Valid) {M D k : ℕ} {h ε : ℝ}
    (hK : p.K k ≤ p.N k ^ ε)
    (hw : ∃ a : Atlas p k, 1 ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
      (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.TrueAt M D p.L) : TerminalAt p M D h ε k := by
  obtain ⟨a, hκ1, hκ, hT, htrue⟩ := hw
  refine ⟨a.enlarge (max a.κ (p.K k)), ?_, ?_, ?_, hT,
    htrue.enlarge hp hκ1 (le_max_left _ _)⟩
  · exact hκ1.trans (le_max_left _ _)
  · exact le_max_right _ _
  · exact max_le hκ hK

/-- Subpower control of K repairs the missing K lower bound uniformly in every tolerance. -/
theorem terminal_of_weak {p : Data} (hp : p.Valid) {h : ℝ}
    (hw : ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
      ∃ a : Atlas p k, 1 ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
        (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.TrueAt M D p.L) : Terminal p h := by
  obtain ⟨M, D, hw⟩ := hw
  refine ⟨M, D, fun ε hε => ?_⟩
  have hK : ∀ᶠ k in Filter.atTop, p.K k ≤ p.N k ^ ε := hp.2.2.1.2 ε hε
  exact ((hw ε hε).and_eventually hK).mono
    (fun _ hk => terminalAt_of_weak hp hk.2 hk.1)

end Submission.Obl.k4_finite_width_path_realization
