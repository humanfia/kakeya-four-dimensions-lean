/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUniformFirstJet.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUniformFirstJet.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformRangeHierarchy
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformResidualRange
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPrunedHierarchy
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetCommonRow
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetBudget
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetOutput
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDyadicTimeGrid

/-! One subpower original first-jet certificate before all measurable worlds. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts

theorem uniform_original_scalar_first_jet_between_powers_all_labels
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) (m : ℕ) :
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧ SubpowerBound N H ∧
      ∀ᶠ k in atTop, ∀ (Λ : Type*) [MeasurableSpace Λ],
        ∀ (D : ScalarMotion Λ) (ν : Measure Λ) [IsProbabilityMeasure ν]
          (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (S : ℝ → Set ℝ) (ζ : ℝ)
          (start : Fin m → ℕ) (read : Fin m),
          ScalarNormalHyp D ν E F S (K k) ζ d → 0 < ζ →
          (K k)⁻¹ ≤ (ν.prod volume).real E → ζ ≤ N k ^ (-(4 * b)) →
          (∀ i, N k ^ (-b) ≤ scalarDyadicLength (start i)) →
          (∀ i, scalarDyadicLength (start i) ≤ N k ^ (-a)) →
          ScalarFirstJetOutput D ν E F start read d (H k) := by
  obtain ⟨steps, hsteps⟩ := exists_uniform_scalar_dyadic_bridge_length ha hab
  let rows := Fintype.card (ScalarBridgeLabels m steps)
  have hrows : 0 < rows := Fintype.card_pos
  have hrows1 : (1 : ℝ) ≤ rows := by exact_mod_cast (Nat.succ_le_iff.mpr hrows : 1 ≤ rows)
  obtain ⟨B, hB, hKB, hBsub, hhierarchy⟩ :=
    uniform_original_scalar_grid_hierarchy_between_powers_all_labels
      N K hN hNt hK hsub ha hab hd0 hd rows
  let P : ℕ → ℝ := fun k => 4 * (rows : ℝ) * B k
  have hBP (k : ℕ) : B k ≤ P k := by
    dsimp only [P]
    have hb : 0 ≤ B k := zero_le_one.trans (hB k)
    have hh := mul_le_mul_of_nonneg_right hrows1 hb
    nlinarith
  have hP : ∀ k, 1 ≤ P k := fun k => (hB k).trans (hBP k)
  have hKP : ∀ k, K k ≤ P k := fun k => (hKB k).trans (hBP k)
  have hPsub : SubpowerBound N P :=
    subpower_mul (fun k => zero_lt_one.trans_le (hN k))
      (fun _ => by positivity) (fun k => zero_le_one.trans (hB k))
      (subpower_const hNt (4 * (rows : ℝ))) hBsub
  let W : ℕ → ℝ := fun k => scalarBlockFitBound (P k)
  have hW : ∀ k, 1 ≤ W k := fun k => (scalarBlockFitBound_bounds (hP k)).1
  have hWsub : SubpowerBound N W :=
    (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial hN hNt
      ⟨hP, hPsub⟩ (A := 100000) (by norm_num) 10).2
  obtain ⟨Q, hQ, hQsub, hresidual⟩ :=
    uniform_subpower_original_residual_slopes_below_all_labels (ι := ℤ)
      N W hN hNt hW hWsub (a := a / 8) (by positivity) hd0 hd 1
  obtain ⟨hH, hHsub⟩ := scalarFirstJetBudget_subpower N P Q hN hNt hP hQ hPsub hQsub steps
  refine ⟨fun k => scalarFirstJetBudget steps (P k) (Q k), hH, hHsub, ?_⟩
  filter_upwards [hhierarchy, hresidual] with k hGk hRk
  intro Λ _ D ν _ E F S ζ start read hnormal hζ hmass hζN hlow hhigh
  have hNpos : 0 < N k := zero_lt_one.trans_le (hN k)
  have hBpos : 0 < B k := zero_lt_one.trans_le (hB k)
  have hPpos : 0 < P k := zero_lt_one.trans_le (hP k)
  have hQpos : 0 < Q k := zero_lt_one.trans_le (hQ k)
  obtain ⟨imax, _, hmax⟩ := Finset.exists_max_image Finset.univ start ⟨read, Finset.mem_univ _⟩
  let top := start imax
  have hstart : ∀ i, start i ≤ top := fun i => hmax i (Finset.mem_univ _)
  have hweaklow : N k ^ (-(2 * b)) ≤ N k ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)
  have hweakhigh : N k ^ (-a) ≤ N k ^ (-(a / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)
  have hreach : ∀ i, scalarDyadicBridge top (start i) steps = top :=
    hsteps (N k) m top start (hN k) (hweaklow.trans (hlow imax))
      (fun i => (hhigh i).trans hweakhigh)
  let J : Fin rows → ℕ := fun i => 2 ^ scalarBridgeHeight top start i
  have hJ : ∀ i, 0 < J i := fun i => Nat.two_pow_pos _
  have hmeshrange (i : Fin rows) :
      N k ^ (-b) ≤ scalarBridgeMesh top start i ∧ scalarBridgeMesh top start i ≤ N k ^ (-a) :=
    scalarBridgeMesh_bounds top start hstart ⟨hlow imax, hhigh imax⟩ hhigh i
  have hJlow (i : Fin rows) : N k ^ (-b) ≤ 1 / (J i : ℝ) := by
    simpa only [J, scalarBridgeMesh, scalarDyadicLength_eq] using! (hmeshrange i).1
  have hJhigh (i : Fin rows) : 1 / (J i : ℝ) ≤ N k ^ (-a) := by
    simpa only [J, scalarBridgeMesh, scalarDyadicLength_eq] using! (hmeshrange i).2
  have hζJ (i : Fin rows) : ζ ≤ (1 / (J i : ℝ)) ^ 2 :=
    scalar_floor_square_of_power_range hNpos hζN (hweaklow.trans (hJlow i))
  obtain ⟨G⟩ := hGk Λ D ν E F S ζ J hJ hnormal hζ hmass hJlow hJhigh hζJ
  obtain ⟨R, hRm, hRP, hmassR, hfloor⟩ :=
    G.exists_common_current_floor_set_of_pos hnormal.event_measurable hBpos hrows
  have hfloorR : ∀ q ∈ R, ∀ i : Fin rows,
      ENNReal.ofReal (scalarBridgeMesh top start i / P k) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ
          Submission.Obl.k4_scalar_marked_coefficient_smoothing.timeCell
            (2 ^ scalarBridgeHeight top start i)
            (scalarTimeBlockCode (2 ^ scalarBridgeHeight top start i) (by positivity) q.2))) := by
    intro q hq i
    simpa only [P, J, scalarBridgeMesh, scalarDyadicLength_eq] using! hfloor q hq i
  have hζRead : ζ ≤ scalarDyadicLength (start read) ^ 2 :=
    scalar_floor_square_of_power_range hNpos hζN (hweaklow.trans (hlow read))
  have hreading : scalarDyadicLength (start read) ^ (1 / 8 : ℝ) ≤ N k ^ (-(a / 8)) := by
    calc
      _ ≤ (N k ^ (-a)) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow (scalarDyadicLength_pos _).le (hhigh read) (by norm_num)
      _ = _ := by
        rw [← Real.rpow_mul hNpos.le]
        congr 1
        ring
  have hconcentration := hRk Λ (scalarDyadicLength (start read) ^ (1 / 8 : ℝ))
    (Real.rpow_pos_of_pos (scalarDyadicLength_pos _) _) hreading
  obtain ⟨R', hR'm, hR'R, hmassR', htaylor, L, hL, hcover⟩ :=
    ScalarGridHierarchy.exists_common_row_first_jet_restriction
      (m := m) (steps := steps) (top := top) (start := start) hstart hreach
      (zero_le_one.trans (hB k)) G read hnormal (hK k) hζ hd0 hd (hP k)
      (hKP k) (hBP k) (inv_nonneg.mpr hQpos.le) hRm hRP hfloorR hζRead hconcentration
  obtain ⟨hU1, hBU, hMassU, hCountU, hTaylorU, hReadU⟩ :=
    scalarFirstJetBudget_bounds (steps := steps) (hP k) (hQ k)
      (zero_le_one.trans (hB k)) (hBP k) (zero_le_one.trans (hK k)) (hKP k)
  have hmassLower : (40000 * B k * P k ^ 6 * Q k)⁻¹ ≤ (ν.prod volume).real R' := by
    calc
      _ = (Q k)⁻¹ / (20000 * P k ^ 6) * (2 * B k)⁻¹ := by field_simp <;> ring
      _ ≤ (Q k)⁻¹ / (20000 * P k ^ 6) * (ν.prod volume).real R :=
        mul_le_mul_of_nonneg_left hmassR (by positivity)
      _ ≤ _ := hmassR'
  have hmassOutput : (scalarFirstJetBudget steps (P k) (Q k))⁻¹ ≤ (ν.prod volume).real R' :=
    (inv_anti₀ (by positivity : 0 < 40000 * B k * P k ^ 6 * Q k) hMassU).trans hmassLower
  refine ⟨R', fun q hq => (hRP (hR'R hq)).1, hR'm,
    ENNReal.ofReal_le_of_le_toReal hmassOutput, G.slope (scalarBridgeTopIndex m steps),
    G.measurable_slope _, ?_, ?_, L, fun t z => (hL t z).trans hCountU, ?_⟩
  · intro q hq
    exact (G.bounded (scalarBridgeTopIndex m steps) q.2).1.trans hBU
  · intro i j q hq q' hq' hqi hq'i
    have hqtime := G.unit_time (hRP (hR'R hq)).2.2
    have hq'time := G.unit_time (hRP (hR'R hq')).2.2
    have hcode := scalarTimeBlockCode_eq_of_common_dyadic_interval hqtime hq'time hqi hq'i
    exact (htaylor i q hq q' hq' hcode).trans
      (mul_le_mul_of_nonneg_right hTaylorU (Real.rpow_nonneg (scalarDyadicLength_pos _).le _))
  · intro q hq
    obtain ⟨v, hv, hdist⟩ := hcover q hq
    exact ⟨v, hv, hdist.trans
      (mul_le_mul_of_nonneg_right hReadU (Real.rpow_nonneg (scalarDyadicLength_pos _).le _))⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
