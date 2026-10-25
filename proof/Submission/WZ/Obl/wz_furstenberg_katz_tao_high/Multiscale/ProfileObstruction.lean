-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale.ProfileObstruction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
A lower terminal slope in the angular profile is incompatible with an
energy inequality valid at every sufficiently coarse cell width.  The
energy hypothesis stays explicit: this file does not establish that it
survives geometric coarsening.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

/-- A frontloaded monotone angular profile has a long terminal interval
with exact lower slope `s-d/4`.  This selects the right endpoint by a
minimum, so it incurs no palette-gap error in the lower-slope bound. -/
theorem frontloading_terminal_interval
    (F t : ℕ → ℝ) {n K : ℕ} {s d L : ℝ}
    (hKn : K ≤ n) (hL : 0 < L) (hd : 0 < d) (hds : d ≤ s) (hs : s < 1)
    (htK : 0 ≤ t K) (htn : t n = L) (hFn : F n = s * L)
    (htmono : ∀ i j, i ≤ j → j ≤ n → t i ≤ t j)
    (hFmono : ∀ i j, i ≤ j → j ≤ n → F i ≤ F j)
    (hfront : s * t K + d * L ≤ F K) :
    ∃ a : ℕ, K < a ∧ a ≤ n ∧ 3 * d * L / 4 ≤ t a - t K ∧
      ∀ i, K ≤ i → i ≤ a →
        F a - (s - d / 4) * (t a - t i) ≤ F i := by
  classical
  let β := s - d / 4
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hβ1 : β ≤ 1 := by dsimp [β]; linarith
  let T := Finset.Icc K n
  have hnT : n ∈ T := Finset.mem_Icc.mpr ⟨hKn, le_rfl⟩
  obtain ⟨a, haT, hmin⟩ := Finset.exists_min_image T (fun i => F i - β * t i) ⟨n, hnT⟩
  obtain ⟨hKa, han⟩ := Finset.mem_Icc.mp haT
  have ham := hmin n hnT
  rw [htn, hFn] at ham
  have htKa := htmono K a hKa han
  have hFKa := hFmono K a hKa han
  have hspan : 3 * d * L / 4 ≤ t a - t K := by
    have hm : β * (t a - t K) ≤ t a - t K :=
      mul_le_of_le_one_left (sub_nonneg.mpr htKa) hβ1
    dsimp [β] at ham hm
    nlinarith only [hfront, ham, hFKa, hm, mul_nonneg hd.le htK]
  have hKalt : K < a := lt_of_le_of_ne hKa (by
    intro h
    rw [← h, sub_self] at hspan
    have : 0 < 3 * d * L / 4 := by positivity
    linarith)
  refine ⟨a, hKalt, han, hspan, ?_⟩
  intro i hKi hia
  have hh := hmin i (Finset.mem_Icc.mpr ⟨hKi, hia.trans han⟩)
  dsimp [β] at hh
  linarith

/-- Compare a cell-energy witness with a minimum of the adjusted point
profile.  Near witnesses contradict the difference of angular exponents;
far witnesses contradict the ambient Lipschitz bound. -/
theorem no_cell_energy_witness_at_minimum
    (G F : ℝ → ℝ) {s β a ℓ h E y : ℝ}
    (_hℓa : ℓ ≤ a) (hhy : h ≤ y) (hya : y ≤ a)
    (hnear : y ≤ ℓ → G h - β * h ≤ G y - β * y + E)
    (hpoint : y - E ≤ G y) (hpointUpper : G h ≤ 2 * h + E)
    (hbush : s * h - E ≤ F h)
    (htail : ∀ z ∈ Set.Icc 0 ℓ, F a - β * z - E ≤ F (a - z))
    (hlip : ∀ u v, 0 ≤ u → u ≤ v → v ≤ a → F v - F u ≤ v - u)
    (hh0 : 0 ≤ h) (hℓ0 : 0 ≤ ℓ)
    (hgap : 4 * E < (s - β) * h)
    (hfar : (2 - s) * h + 5 * E < (1 - β) * ℓ) :
    F a + G h - F h + E < G y + F (a - y) := by
  by_cases hyℓ : y ≤ ℓ
  · have hm := hnear hyℓ
    have ht := htail y ⟨hh0.trans hhy, hyℓ⟩
    nlinarith only [hm, ht, hbush, hgap]
  · have hyℓ' : ℓ ≤ y := (lt_of_not_ge hyℓ).le
    have ht := htail ℓ ⟨hℓ0, le_rfl⟩
    have hf := hlip (a - y) (a - ℓ) (by linarith)
      (by linarith) (by linarith)
    nlinarith only [ht, hf, hpoint, hpointUpper, hbush, hfar]

/-- The numerical location estimate for the adjusted-profile minimum. -/
theorem profile_minimum_location
    {Gh GH β h H E : ℝ}
    (hlower : h - E ≤ Gh) (hupper : GH ≤ 2 * H + E)
    (hmin : Gh - β * h ≤ GH - β * H) :
    (1 - β) * h ≤ (2 - β) * H + 2 * E := by
  nlinarith only [hlower, hupper, hmin]

/-- On any finite palette containing a sufficiently small starting scale,
a lower-slope terminal interval produces a cell width where the proposed
coarsened energy bound fails.  All error budgets are explicit. -/
theorem exists_cell_energy_obstruction
    (S : Finset ℝ) (G F : ℝ → ℝ) {s β a ℓ H E : ℝ}
    (hs : s < 1) (hβ : β < s) (hE : 0 ≤ E)
    (hH : 0 < H) (hHℓ : H ≤ ℓ) (hHS : H ∈ S) (hℓa : ℓ ≤ a)
    (hpoint : ∀ t ∈ S, H ≤ t → t ≤ a → t - E ≤ G t)
    (hpointUpper : ∀ t ∈ S, H ≤ t → t ≤ ℓ → G t ≤ 2 * t + E)
    (hbush : ∀ t ∈ S, H ≤ t → t ≤ ℓ → s * t - E ≤ F t)
    (htail : ∀ z ∈ Set.Icc 0 ℓ, F a - β * z - E ≤ F (a - z))
    (hlip : ∀ u v, 0 ≤ u → u ≤ v → v ≤ a → F v - F u ≤ v - u)
    (hgap : 4 * E < (s - β) * H)
    (hbudget : (2 - s) * ((2 - β) * H + 2 * E) + 5 * E * (1 - β) <
      (1 - β) ^ 2 * ℓ) :
    ∃ h ∈ S, H ≤ h ∧ h ≤ ℓ ∧
      ∀ y ∈ S, h ≤ y → y ≤ a →
        F a + G h - F h + E < G y + F (a - y) := by
  classical
  let T := S.filter (fun t => H ≤ t ∧ t ≤ ℓ)
  have hHT : H ∈ T := Finset.mem_filter.mpr ⟨hHS, le_rfl, hHℓ⟩
  obtain ⟨h, hhT, hmin⟩ := Finset.exists_min_image T (fun t => G t - β * t) ⟨H, hHT⟩
  obtain ⟨hhS, hHh, hhℓ⟩ := Finset.mem_filter.mp hhT
  have hβ1 : 0 < 1 - β := by linarith
  have h2s : 0 ≤ 2 - s := by linarith
  have hlocation := profile_minimum_location
    (hpoint h hhS hHh (hhℓ.trans hℓa))
    (hpointUpper H hHS le_rfl hHℓ) (hmin H hHT)
  have hfar : (2 - s) * h + 5 * E < (1 - β) * ℓ := by
    have hmul := mul_le_mul_of_nonneg_left hlocation h2s
    have hh : ((2 - s) * h + 5 * E) * (1 - β) <
        ((1 - β) * ℓ) * (1 - β) := by
      nlinarith only [hmul, hbudget]
    exact (mul_lt_mul_iff_left₀ hβ1).mp hh
  have hgap' : 4 * E < (s - β) * h :=
    hgap.trans_le (mul_le_mul_of_nonneg_left hHh (sub_pos.mpr hβ).le)
  refine ⟨h, hhS, hHh, hhℓ, ?_⟩
  intro y hy hhy hya
  apply no_cell_energy_witness_at_minimum G F hℓa hhy hya
    (fun hyℓ => ?_) (hpoint y hy (hHh.trans hhy) hya)
    (hpointUpper h hhS hHh hhℓ) (hbush h hhS hHh hhℓ)
    htail hlip (hH.le.trans hHh) (hH.le.trans hHℓ) hgap' hfar
  exact (hmin y (Finset.mem_filter.mpr ⟨hy, hHh.trans hhy, hyℓ⟩)).trans
    (le_add_of_nonneg_right hE)

/-- Choose the starting-scale window and error tolerance before selecting
an actual palette point in that window. -/
theorem profile_obstruction_budgets {s β ℓ : ℝ}
    (hs : s < 1) (hβ : β < s) (hℓ : 0 < ℓ) :
    ∃ H₀ E₀ : ℝ, 0 < H₀ ∧ 0 < E₀ ∧ 2 * H₀ ≤ ℓ ∧
      ∀ H E : ℝ, H₀ ≤ H → H ≤ 2 * H₀ → E ≤ E₀ →
        4 * E < (s - β) * H ∧
        (2 - s) * ((2 - β) * H + 2 * E) + 5 * E * (1 - β) <
          (1 - β) ^ 2 * ℓ := by
  let A := (2 - s) * (2 - β)
  let B := 2 * (2 - s) + 5 * (1 - β)
  let T := (1 - β) ^ 2 * ℓ
  have h2s : 0 < 2 - s := by linarith
  have h2β : 0 < 2 - β := by linarith
  have h1β : 0 < 1 - β := by linarith
  have hA : 0 < A := mul_pos h2s h2β
  have hB : 0 < B := by dsimp [B]; positivity
  have hT : 0 < T := mul_pos (pow_pos h1β 2) hℓ
  let H₀ := min (ℓ / 4) (T / (16 * A))
  have hH₀ : 0 < H₀ := lt_min (by positivity) (by positivity)
  have hHℓ : 2 * H₀ ≤ ℓ := by
    have := min_le_left (ℓ / 4) (T / (16 * A))
    dsimp [H₀]
    linarith
  have hHA : A * H₀ ≤ T / 16 := by
    have hh : H₀ ≤ T / (16 * A) := min_le_right _ _
    rw [le_div_iff₀ (by positivity : 0 < 16 * A)] at hh
    nlinarith
  let E₀ := min ((s - β) * H₀ / 8) (T / (8 * B))
  have hE₀ : 0 < E₀ := lt_min (by have := sub_pos.mpr hβ; positivity) (by positivity)
  refine ⟨H₀, E₀, hH₀, hE₀, hHℓ, ?_⟩
  intro H E hHlow hHhigh hE
  have hEg : E ≤ (s - β) * H₀ / 8 := hE.trans (min_le_left _ _)
  have hEB : B * E ≤ T / 8 := by
    have hh : E ≤ T / (8 * B) := hE.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity : 0 < 8 * B)] at hh
    nlinarith
  have hAH : A * H ≤ T / 8 := by
    have hh := mul_le_mul_of_nonneg_left hHhigh hA.le
    nlinarith only [hh, hHA]
  constructor
  · have hpos : 0 < (s - β) * H₀ := mul_pos (sub_pos.mpr hβ) hH₀
    have hh := mul_le_mul_of_nonneg_left hHlow (sub_pos.mpr hβ).le
    nlinarith only [hEg, hpos, hh]
  · change (2 - s) * ((2 - β) * H + 2 * E) + 5 * E * (1 - β) < T
    have hid : (2 - s) * ((2 - β) * H + 2 * E) + 5 * E * (1 - β) =
        A * H + B * E := by dsimp [A, B]; ring
    rw [hid]
    linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
