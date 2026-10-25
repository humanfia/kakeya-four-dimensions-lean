import Submission.Obl.k4_wide_three_layer_scalar_inputs.WitnessFreezing
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.PredictionData
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.FromPartition

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context

open Set MeasureTheory MvPolynomial Filter
open Inherited.Native

noncomputable section

variable {α : Type} [MeasurableSpace α] (W : Context α)

/-- The physical frame remains the original true block throughout the witness construction. -/
def predictionFrame (L : Fin 4 → ℝ) : Support.Frame :=
  Support.blockFrame W.cfg W.k W.s W.i L

def predictionPolynomial (L : Fin 4 → ℝ) (γ : W.Coarse) : Fin 6 → ℝ :=
  KeyFrame.nativeChartPolynomial (W.predictionFrame L).cellFrame
    (W.cfg.F W.k W.s W.i) (W.layers.G 0 (W.coarseIndex γ)) W.χ (W.key γ)

def predictionPC (L : Fin 4 → ℝ) (γ : W.Coarse) : Fin 6 → ℝ :=
  KeyFrame.baseCoefficients (W.predictionPolynomial L γ)

def predictionTC (L : Fin 4 → ℝ) (γ : W.Coarse) : Fin 4 → ℝ :=
  KeyFrame.transverseCoefficients (W.predictionPolynomial L γ)

theorem predictionTC_two (L : Fin 4 → ℝ) (γ : W.Coarse) : W.predictionTC L γ 2 = 0 := rfl

theorem predictionFrame_eq_prefix {H : ℝ} (P : Support.BlockPrefix W.cfg W.k W.s H)
    (hi : P.i = W.i) : W.predictionFrame P.L = P.frame := by
  simp only [predictionFrame, Support.BlockPrefix.frame, hi]

/-- Eligibility of the actual coarse witness bounds every recovered discrepancy coefficient. -/
theorem prediction_discrepancy_bound (L : Fin 4 → ℝ) (γ : W.Coarse) :
    ∀ e, |KeyFrame.nativeDiscrepancy (W.predictionFrame L).cellFrame
      (W.cfg.F W.k W.s W.i) (W.layers.G 0 (W.coarseIndex γ)) W.χ (W.key γ) e| ≤ W.Mst := by
  intro e
  have h := γ.2.2.1
  have he : |blockKeyCoeff (W.cfg.F W.k W.s W.i) W.a W.χ W.m W.q W.t₀ (W.key γ) e -
      sheetKeyCoeff (W.layers.G 0 (W.coarseIndex γ)) W.a W.χ W.m W.q W.t₀ (W.key γ) e| < W.Mst :=
    lt_of_not_ge (fun hh => h ⟨e, hh⟩)
  simpa only [KeyFrame.nativeDiscrepancy, predictionFrame, Support.blockFrame,
    Support.Frame.cellFrame, a, m, q, g, t₀, slotLen, slotStart, Pi.sub_apply,
    abs_sub_comm] using he.le

/-- Whole original block geometry and the occupied coarse label pay the prediction
coefficients, without choosing any new graph, key or incidence. -/
theorem prediction_coefficients_bound (hv : W.cfg.Valid) {Rcap K : ℝ}
    (hB : BlocksAt W.cfg.comparisonData W.k W.s Rcap) (L : Fin 4 → ℝ)
    (hs : 0 ≤ W.s) (hKK : W.cfg.K W.k ≤ K)
    (hproj : W.cfg.N W.k ^ W.ε ≤ K) (hqg : W.q ≤ K * W.g)
    (hχ : 0 < W.χ) (hχm : W.χ ≤ W.m) (γ : W.Coarse) :
    (∀ e, |W.predictionPC L γ e| ≤ 3888 * W.Mst * K ^ 8) ∧
    (∀ e, |W.predictionTC L γ e| ≤ 3888 * W.Mst * K ^ 8) := by
  have hK : 1 ≤ K := (hv.subpower.1 W.k).trans hKK
  have hN : 0 < W.cfg.N W.k := by linarith [hv.scale W.k]
  have hq : 0 < W.q := slotLen_pos W.cfg.comparisonData W.k W.s
  have hg : 0 < W.g := Real.rpow_pos_of_pos hN _
  have hg₁ : W.g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [hv.scale W.k]) (by nlinarith [hv.rate_pos])
  obtain ⟨l, hlB, hlC, hkey, -⟩ := γ.2.2.2
  have hb : |W.cfg.b W.k l 3| ≤ K :=
    (((W.layers.piece 0 (W.coarseIndex γ)).1 l hlC).2.2.2 3).trans hproj
  have hu := slot_unit W.cfg.comparisonData W.k W.s (W.cfg.j W.k W.s W.i)
  change 0 ≤ W.t₀ ∧ W.t₀ + W.q ≤ 1 at hu
  have ht₀ : W.t₀ ∈ Icc (0 : ℝ) 1 := ⟨hu.1, by linarith [hu.2]⟩
  have htmid : W.t₀ + W.q / 2 ∈ Icc W.t₀ (W.t₀ + W.q) := by
    constructor <;> linarith
  have ht₀' : W.t₀ ∈ W.cfg.comparisonData.I (W.cfg.T W.k W.s) (W.cfg.j W.k W.s W.i) := by
    rw [I_eq_slot]
    change W.t₀ ∈ Icc W.t₀ (W.t₀ + W.q)
    exact ⟨le_rfl, by linarith⟩
  have htmid' : W.t₀ + W.q / 2 ∈
      W.cfg.comparisonData.I (W.cfg.T W.k W.s) (W.cfg.j W.k W.s W.i) := by
    rw [I_eq_slot]
    exact htmid
  have hgeo₀ := (hB.geom W.i l ((hB.sets W.i).2.2 hlB) W.t₀ ht₀').2.1
  have hgeom := (hB.geom W.i l ((hB.sets W.i).2.2 hlB) _ htmid').1
  have hcenter := hB.center W.i
  have hmid : (((W.cfg.j W.k W.s W.i : ℕ) : ℝ) + 1 / 2) *
      ((2 : ℝ) ^ W.cfg.T W.k W.s)⁻¹ = W.t₀ + W.q / 2 := by
    dsimp [t₀, q, slotStart, slotLen]
    rw [div_eq_mul_inv]
    ring
  change |W.cfg.c W.k W.s W.i 3 + W.cfg.c W.k W.s W.i 0 +
      ((((W.cfg.j W.k W.s W.i : ℕ) : ℝ) + 1 / 2) * ((2 : ℝ) ^ W.cfg.T W.k W.s)⁻¹) *
        W.cfg.c W.k W.s W.i 1| +
      |W.cfg.c W.k W.s W.i 4 -
        (((W.cfg.j W.k W.s W.i : ℕ) : ℝ) + 1 / 2) * ((2 : ℝ) ^ W.cfg.T W.k W.s)⁻¹| ≤
      W.cfg.K W.k * W.q at hcenter
  rw [hmid] at hcenter
  have hβ := KeyFrame.native_beta_bound (W.predictionFrame L).cellFrame
    (W.cfg.b W.k) l (W.key γ) hK hq hg hg₁ hqg hχ hχm hkey
    (show |W.t₀| ≤ 1 from abs_le.mpr ⟨by linarith [ht₀.1], ht₀.2⟩)
    ((hB.c_bd W.i 4).trans hKK) hb
    (hcenter.trans (mul_le_mul_of_nonneg_right hKK hq.le))
    (by
      change |W.cfg.b W.k l 1 + W.t₀ * W.cfg.b W.k l 4 -
        (W.cfg.c W.k W.s W.i 2 + W.t₀ * W.cfg.c W.k W.s W.i 3 +
          W.cfg.c W.k W.s W.i 4 * (W.cfg.b W.k l 0 + W.t₀ * W.cfg.b W.k l 3))| ≤ K * W.m
      calc
        _ = |(W.cfg.comparisonData.x W.k l W.t₀) 2 - W.cfg.c W.k W.s W.i 2 -
          W.t₀ * W.cfg.c W.k W.s W.i 3 - W.cfg.c W.k W.s W.i 4 *
            (W.cfg.comparisonData.x W.k l W.t₀) 1| := by congr 1; dsimp [Inherited.Data.x]; ring
        _ ≤ W.cfg.K W.k * W.m := by simpa only [m, q, g, slotLen, mul_assoc] using hgeo₀
        _ ≤ _ := mul_le_mul_of_nonneg_right hKK (mul_pos hq hg).le)
    (hgeom.trans (mul_le_mul_of_nonneg_right hKK hq.le))
  have hr := W.prediction_discrepancy_bound L γ
  have hMst : 0 ≤ W.Mst := (abs_nonneg _).trans (hr 0)
  exact KeyFrame.native_coefficients_bound (W.predictionFrame L).cellFrame
    (W.cfg.F W.k W.s W.i) (W.layers.G 0 (W.coarseIndex γ)) W.χ (W.key γ) hK hMst hβ hr

/-- The two original fine fits will use this same error at the original key. -/
def freezingError : ℝ := 98304 * W.E * (W.q + W.m / W.D)

/-- A prediction fit for every original fine witness and incidence. -/
def PredictionFits (L : Fin 4 → ℝ) (chartError : ℝ) : Prop :=
  ∀ (γ : W.Coarse) (h : Fin 3) (j : Fin (W.layers.np h)), W.fineValid γ h j →
    ∀ (l : α) (t : ℝ), l ∈ W.layers.C h j →
      slotKey (W.cfg.b W.k) W.χ W.m W.t₀ l = W.key γ →
      |W.cfg.b W.k l 4 + W.cfg.b W.k l 0| ≤ W.ζ → t ∈ Icc W.t₀ (W.t₀ + W.q) →
      |(W.predictionFrame L).resid (W.cfg.b W.k l) t -
        Support.quadZ (W.predictionPC L γ) ((W.predictionFrame L).zt t)
          ((W.predictionFrame L).zZ (W.cfg.b W.k l) t) - W.physicalOffset γ h j / W.a -
        Support.transv (W.predictionTC L γ) ((W.predictionFrame L).zt t)
          ((W.predictionFrame L).zZ (W.cfg.b W.k l) t)
          ((W.predictionFrame L).tr (W.cfg.b W.k l) t)| ≤
        (W.cfg.N W.k ^ W.ε * W.cfg.N W.k ^ (-(![W.s, W.s + W.u, W.s + W.v] h)) +
          W.freezingError) / W.a + chartError

/-- The concrete whole-key freezing bound transfers to the original label, with the
offset normalized by the width of the same original block. -/
theorem prediction_freezing_at_label (hN : 0 < W.cfg.N W.k)
    (hχ : 0 < W.χ) (hD : 0 < W.D) (hmD : W.m ≤ W.D)
    (hdrift : W.ζ + W.χ ≤ W.D / 4) (hsmall : W.q * (W.ζ + W.χ) ≤ W.m / 2)
    (γ : W.Coarse) (h : Fin 3) (j : Fin (W.layers.np h)) (hj : W.fineValid γ h j)
    {l : α} {t : ℝ} (hk : slotKey (W.cfg.b W.k) W.χ W.m W.t₀ l = W.key γ)
    (hh : |W.cfg.b W.k l 4 + W.cfg.b W.k l 0| ≤ W.ζ)
    (ht : t ∈ Icc W.t₀ (W.t₀ + W.q)) :
    |eval ![t, W.cfg.b W.k l 1 + t * W.cfg.b W.k l 4] (W.layers.G h j) -
      eval ![t, W.cfg.b W.k l 1 + t * W.cfg.b W.k l 4]
        (W.layers.G 0 (W.coarseIndex γ)) - W.a * (W.physicalOffset γ h j / W.a)| ≤
      W.freezingError := by
  have ha : W.a ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  have hm : 0 < W.m := mul_pos (slotLen_pos W.cfg.comparisonData W.k W.s)
    (Real.rpow_pos_of_pos hN _)
  rw [mul_div_cancel₀ _ ha]
  exact W.fine_freezing_at_label hχ hm γ h j
    (W.fine_key_freezing hN hχ hD hmD hdrift γ h j hj) hk hh hsmall ht

/-- An explicit error bound for the actual witness predictions on all original
incidences. Both fine colors use one coarse polynomial. -/
theorem prediction_fits (hv : W.cfg.Valid) {Rcap K B Lb : ℝ}
    (hB : BlocksAt W.cfg.comparisonData W.k W.s Rcap) (L : Fin 4 → ℝ)
    (hL : HorizontalForm (W.cfg.F W.k W.s W.i) L)
    (hKK : W.cfg.K W.k ≤ K) (hproj : W.cfg.N W.k ^ W.ε ≤ K)
    (hχ : 0 < W.χ) (hχ₁ : W.χ ≤ 1) (hD : 0 < W.D) (hmD : W.m ≤ W.D)
    (hdrift : W.ζ + W.χ ≤ W.D / 4) (hsmall : W.q * (W.ζ + W.χ) ≤ W.m / 2)
    (hcoeff : ∀ (γ : W.Coarse) e, |(W.layers.G 0 (W.coarseIndex γ)).coeff e| ≤ B)
    (hL₂ : |L 2| ≤ Lb) (hL₃ : |L 3| ≤ Lb) :
    W.PredictionFits L ((48 * B * K ^ 2 + 8 * Lb * K) * W.χ / W.a) := by
  have hN : 0 < W.cfg.N W.k := by linarith [hv.scale W.k]
  have hK : 1 ≤ K := (hv.subpower.1 W.k).trans hKK
  have hq : 0 < W.q := slotLen_pos W.cfg.comparisonData W.k W.s
  have hg : 0 < W.g := Real.rpow_pos_of_pos hN _
  have ha : 0 < W.a := Real.rpow_pos_of_pos hN _
  intro γ h j hj l t hl hk hh ht
  have hu := slot_unit W.cfg.comparisonData W.k W.s (W.cfg.j W.k W.s W.i)
  change 0 ≤ W.t₀ ∧ W.t₀ + W.q ≤ 1 at hu
  have htunit : t ∈ Icc (0 : ℝ) 1 := ⟨hu.1.trans ht.1, ht.2.trans hu.2⟩
  have hb : ∀ e, |W.cfg.b W.k l e| ≤ W.cfg.N W.k ^ W.ε :=
    ((W.layers.piece h j).1 l hl).2.2.2
  have hY := shortDefs_coord_bound hb (by linarith : 2 * W.cfg.N W.k ^ W.ε ≤ 2 * K)
    htunit 1 4
  have hfit := W.datum.fit hl htunit
  have hfreeze := W.prediction_freezing_at_label hN hχ hD hmD hdrift hsmall γ h j hj hk hh ht
  have hc₄ : |(W.predictionFrame L).c 4| ≤ 2 * K :=
    ((hB.c_bd W.i 4).trans hKK).trans (by linarith)
  have hp := KeyFrame.native_compared_fit (W.predictionFrame L) (W.cfg.b W.k) l
    (W.cfg.F W.k W.s W.i) hL (W.layers.G 0 (W.coarseIndex γ))
    (W.datum.degree 0 (W.coarseIndex γ)) (W.layers.G h j) (W.key γ) hq.ne' hg.ne' ha
    hχ hχ₁ (by linarith : 1 ≤ 2 * K) hk htunit (hcoeff γ) hL₂ hL₃ hY hc₄ hfit hfreeze
  convert hp using 1 <;>
    dsimp only [predictionPC, predictionTC, predictionPolynomial, predictionFrame, Support.blockFrame, a] <;>
    ring

/-- The fixed physical horizon makes the chart term negligible uniformly in all
actual witness contexts, coarse labels, fine colors and original incidences. -/
theorem eventually_prediction_fits (cfg : Data α) (hv : cfg.Valid)
    {s₀ sp M η : ℝ} (hs₀ : 0 < s₀) (hsp : sp < 3 * s₀ / 2)
    (hM : 100 * s₀ < M) (hη : 0 < η) (hηs₀ : 2 * η ≤ s₀) :
    ∀ᶠ k in atTop, ∀ W : Context α, W.cfg = cfg → W.k = k → W.s = sp →
      W.χ = cfg.N k ^ (-M) → ∀ (Rcap K : ℝ),
      BlocksAt W.cfg.comparisonData W.k W.s Rcap →
      ∀ L : Fin 4 → ℝ, HorizontalForm (W.cfg.F W.k W.s W.i) L →
      W.cfg.K W.k ≤ K → W.cfg.N W.k ^ W.ε ≤ K → K ≤ cfg.N k ^ η →
      0 < W.D → W.m ≤ W.D → W.ζ + W.χ ≤ W.D / 4 →
      W.q * (W.ζ + W.χ) ≤ W.m / 2 →
      (∀ (γ : W.Coarse) e, |(W.layers.G 0 (W.coarseIndex γ)).coeff e| ≤ cfg.N k ^ (10 * s₀)) →
      |L 2| ≤ cfg.N k ^ (5 * s₀) → |L 3| ≤ cfg.N k ^ (5 * s₀) →
      W.PredictionFits L (cfg.N k ^ (-M / 2)) := by
  have hgrowth := (tendsto_rpow_atTop hη).comp hv.scale_limit
  filter_upwards [KeyFrame.eventually_native_compared_fit cfg.N hv.scale hv.scale_limit hs₀ hsp hM,
    hgrowth.eventually (eventually_ge_atTop (2 : ℝ))] with k hchart htwo
  change 2 ≤ cfg.N k ^ η at htwo
  intro W hcfg hk hs hχeq Rcap K hB L hL hKK hproj hKN hD hmD hdrift hsmall hcoeff hL₂ hL₃
  have hNk : W.cfg.N W.k = cfg.N k := by rw [hcfg, hk]
  have hvW : W.cfg.Valid := hcfg.symm ▸ hv
  have hN : 0 < cfg.N k := by linarith [hv.scale k]
  have hNW : 0 < W.cfg.N W.k := by rw [hNk]; exact hN
  have hK : 1 ≤ K := (hvW.subpower.1 W.k).trans hKK
  have hq : 0 < W.q := slotLen_pos W.cfg.comparisonData W.k W.s
  have hg : 0 < W.g := Real.rpow_pos_of_pos hNW _
  have hχ : 0 < W.χ := by rw [hχeq]; positivity
  have htwoK : 2 * K ≤ cfg.N k ^ (2 * η) := by
    calc
      _ ≤ cfg.N k ^ η * cfg.N k ^ η := mul_le_mul htwo hKN (by linarith) (by positivity)
      _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
  have ha : (W.predictionFrame L).a = cfg.N k ^ (-sp) := by
    change W.cfg.N W.k ^ (-W.s) = _
    rw [hNk, hs]
  have hc₄ : |(W.predictionFrame L).c 4| ≤ cfg.N k ^ (2 * η) :=
    ((hB.c_bd W.i 4).trans hKK).trans ((by linarith : K ≤ 2 * K).trans htwoK)
  intro γ h j hj l t hl hkey hh ht
  have hu := slot_unit W.cfg.comparisonData W.k W.s (W.cfg.j W.k W.s W.i)
  change 0 ≤ W.t₀ ∧ W.t₀ + W.q ≤ 1 at hu
  have htunit : t ∈ Icc (0 : ℝ) 1 := ⟨hu.1.trans ht.1, ht.2.trans hu.2⟩
  have hb : ∀ e, |W.cfg.b W.k l e| ≤ W.cfg.N W.k ^ W.ε :=
    ((W.layers.piece h j).1 l hl).2.2.2
  have hY := (shortDefs_coord_bound hb (by linarith : 2 * W.cfg.N W.k ^ W.ε ≤ 2 * K)
    htunit 1 4).trans htwoK
  have hfreeze := W.prediction_freezing_at_label hNW hχ hD hmD hdrift hsmall γ h j hj hkey hh ht
  have hp := hchart (2 * η) (by positivity) hηs₀ α (W.predictionFrame L) (W.cfg.b W.k) l
    hq.ne' hg.ne' ha (W.cfg.F W.k W.s W.i) hL (W.layers.G 0 (W.coarseIndex γ))
    (W.datum.degree 0 (W.coarseIndex γ)) (hcoeff γ) hL₂ hL₃ hc₄ (W.layers.G h j) (W.key γ)
    t (W.physicalOffset γ h j / W.a)
    (W.cfg.N W.k ^ W.ε * W.cfg.N W.k ^ (-(![W.s, W.s + W.u, W.s + W.v] h)))
    W.freezingError (by rw [← hχeq]; exact hkey) htunit hY (W.datum.fit hl htunit) hfreeze
  simpa only [← hχeq, predictionPC, predictionTC, predictionPolynomial,
    predictionFrame, Support.blockFrame, a] using hp

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context
