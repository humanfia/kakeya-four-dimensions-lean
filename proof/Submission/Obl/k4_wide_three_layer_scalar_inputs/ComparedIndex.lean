import Submission.Obl.k4_wide_three_layer_scalar_inputs.ComparisonAssembly
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ComparisonNumerics
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ComparisonOutputs
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ComparisonEnvironment
import Submission.Obl.k4_wide_three_layer_scalar_inputs.BoundedKeys

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory Filter
open Inherited.Native Inherited.Core

noncomputable section

open scoped Classical

namespace ComparedLayers

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ}
    {σ R χ D s u v : ℝ}

/-- The concrete finite witness system on the selected original block. -/
def shortContext (L : ComparedLayers cfg k σ R χ D ![s, s + u, s + v] s u)
    (i : Fin (cfg.n k s)) (η ξ : ℝ) : ShortWitnesses.Context α where
  cfg := cfg
  k := k
  s := s
  u := u
  v := v
  ε := σ
  R := R
  χ := χ
  D := D
  K₁ := cfg.N k ^ (10 * η)
  Mst := cfg.N k ^ ξ
  layers := L
  i := i
  KB := boundedKeys χ
    (slotLen cfg.comparisonData k s * cfg.N k ^ (-cfg.κ * s)) (4 * cfg.N k ^ η)

end ComparedLayers

namespace ShortWitnesses.Context

variable {α : Type} [MeasurableSpace α]

def exception (W : Context α) : Set (α × ℝ) :=
  shortBad W.cfg.comparisonData W.k W.s W.datum W.m W.K₁ W.Mst W.KB

end ShortWitnesses.Context

/-- All source caps, earlier marginal floors, graph errors and finite
counts are discharged here. The remaining inputs are the actual retained
original prefix and its uniformly negligible chart error. -/
theorem compared_index_of_prefix {α : Type} [MeasurableSpace α] {cfg : Data α}
    (hv : cfg.Valid) {buffer : ℝ} (hb : 100 < buffer)
    (p : Parameters cfg.d cfg.κ cfg.U cfg.e₀ buffer)
    {k : ℕ} {σ R η ξ ηmatch R₀ ε Rcap : ℝ}
    (L : ComparedLayers cfg k σ R (cfg.N k ^ (-p.M)) (cfg.N k ^ (-2 * cfg.κ * p.s₀))
      ![p.s, p.s + p.u, p.s + p.v] p.s p.u)
    (env : ComparisonEnvironment cfg k p.s p.u p.M Rcap)
    (cn : ComparisonNumerics (cfg.N k) (cfg.K k) cfg.d cfg.κ p.s₀ p.s p.u p.v p.M cfg.e₀
      σ η ξ ηmatch R₀ (slotLen cfg.comparisonData k p.s))
    (out : ComparisonOutputs (cfg.N k) (cfg.K k) cfg.d σ η ξ ε p.M)
    (hKN : cfg.K k ≤ cfg.N k ^ σ) (hξv : ξ ≤ p.v)
    (P : Support.BlockPrefix cfg k p.s (cfg.N k ^ ε))
    (hle : P.lam ≤ L.ρs) (hpos : 0 < P.lam univ)
    (hgood : ∀ᵐ z ∂P.lam, z ∉ (L.shortContext P.i η ξ).exception)
    (hfit : (L.shortContext P.i η ξ).PredictionFits P.L (cfg.N k ^ (-p.M / 2))) :
    Nonempty (Support.ComparedBlock cfg k p.s p.u p.v (cfg.N k ^ (-p.M)) (cfg.N k ^ ε)) := by
  let W := L.shortContext P.i η ξ
  letI : IsProbabilityMeasure (W.cfg.π W.k) := env.palette_prob
  have hN : 0 < cfg.N k := by linarith [hv.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [hv.scale k]
  have hq : 0 < W.q := slotLen_pos cfg.comparisonData k p.s
  have hg : 0 < W.g := Real.rpow_pos_of_pos hN _
  have hm : 0 < W.m := mul_pos hq hg
  have ha : 0 < W.a := Real.rpow_pos_of_pos hN _
  have hD : 0 < W.D := Real.rpow_pos_of_pos hN _
  have hχ : 0 < W.χ := Real.rpow_pos_of_pos hN _
  have hH : 1 ≤ cfg.N k ^ η := by linarith [cn.input_one, cn.input_budget]
  have hPH : cfg.N k ^ σ ≤ cfg.N k ^ η := by linarith [cn.input_one, cn.input_budget]
  have hXb : 2 * cfg.N k ^ σ ≤ 2 * cfg.N k ^ η := by linarith
  have hOffsetH : 2 * cfg.N k ^ σ + 1 ≤ cfg.N k ^ η := by
    linarith [cn.input_one, cn.input_budget]
  have hMu : p.u ≤ p.M / 2 := by
    have h100 := (mul_lt_mul_of_pos_right hb p.s₀_pos).trans p.M_lower
    linarith [p.u_lt_s₀, p.s₀_pos]
  have hMv : p.v ≤ p.M / 2 := by linarith [p.v_u]
  have hunit : 0 ≤ W.t₀ ∧ W.t₀ + W.q ≤ 1 := slot_unit cfg.comparisonData k p.s (cfg.j k p.s P.i)
  have hLμ : W.layers.ρs ≤ cfg.μ k := L.le_rho.trans env.rho_le
  have hhor : ∀ᵐ z ∂P.lam, |cfg.b k z.1 4 + cfg.b k z.1 0| ≤ W.ζ :=
    ae_mono (hle.trans hLμ) env.horizontal
  have hnull : W.layers.ρs (horizSet (cfg.b k) W.ζ)ᶜ = 0 :=
    ae_iff.mp (ae_mono hLμ env.horizontal)
  have hsmall : W.q * (W.ζ + W.χ) ≤ W.m / 2 := by
    have hh := mul_le_mul_of_nonneg_left cn.short.jitter_quarter hm.le
    have hi := cn.short.interval_drift
    change W.q * (W.ζ + W.χ) ≤ W.m * cfg.N k ^ (-p.M / 4) at hi
    linarith
  have hkeys : ∀ᵐ z ∂P.lam, slotKey (cfg.b k) W.χ W.m W.t₀ z.1 ∈ W.KB := by
    have hM : 0 < p.M := p.M_pos (by linarith)
    have hχ1 : W.χ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have hD1 : W.D ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1
      (by nlinarith [mul_pos hv.rate_pos p.s₀_pos])
    have hm1 : W.m ≤ 1 := cn.short.m_D.trans hD1
    filter_upwards [ae_mono hle L.cover] with z hz
    obtain ⟨j, hj⟩ := hz 0
    have hparams : ∀ e, |cfg.b k z.1 e| ≤ cfg.N k ^ σ := (W.datum.mem_bins hj).2.2.2
    exact slotKey_mem_boundedKeys hχ hm hχ1 hm1
      ⟨hunit.1, by linarith [hunit.2]⟩ hparams (by linarith [cn.input_budget])
  have hpow10 : (cfg.N k ^ p.s₀) ^ 10 = cfg.N k ^ (10 * p.s₀) := by
    rw [← Real.rpow_mul_natCast hN.le]
    congr 1
    ring
  have hBsh (h : Fin 3) :
      8 * (11 * (160 * cfg.N k ^ σ) / W.width h) ≤ cfg.N k ^ (10 * p.s₀) := by
    have hh := (cn.raw h).sheet_coeff
    rw [hpow10] at hh
    exact hh
  have htol (h : Fin 3) : 1 ≤ W.tolerance h ∧ W.tolerance h ≤ 2 * cfg.N k ^ η :=
    (cn.raw h).sheet_tolerance
  let hn (h : Fin 3) (key : Fin 3 → ℤ) (hk : key ∈ W.KB) :=
    cn.keys h W.t₀ key hunit (boundedKeys_bound hk).1 (boundedKeys_bound hk).2.1
      (W.tolerance h) (W.tolerance h) (htol h).1 (htol h).2 (htol h).1 (htol h).2
  have hdepth (h : Fin 3) : ![p.s, p.s + p.u, p.s + p.v] h ≤ p.s + p.u := by
    fin_cases h
    · change p.s ≤ p.s + p.u
      linarith [p.u_pos]
    · change p.s + p.u ≤ p.s + p.u
      exact le_rfl
    · change p.s + p.v ≤ p.s + p.u
      linarith [p.v_u]
  have hcount : ∀ key ∈ W.KB, ((W.coarseCandidates key).card : ℝ) ≤
      cfg.N k ^ (20 * η) * (cfg.N k ^ ξ / (4 * cfg.N k ^ η)) ^ cfg.d := by
    intro key hk
    exact W.coarse_candidate_count env.measurable hLμ hN rfl hD hXb cn.strip_drift
      cn.whole_key_strip hnull (hBsh 0) key hk (hn 0 key hk)
      (fun sp hs0 hs => env.caps sp hs0 (hs.trans (hdepth 0)))
  have hwide1 : W.freezingError ≤ W.width 1 := cn.wide
  have hwide2 : W.freezingError ≤ W.width 2 := hwide1.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [W, ComparedLayers.shortContext,
      ShortWitnesses.Context.width, ShortWitnesses.Context.depth]; linarith [p.v_u]))
  have ha1 : W.width 1 ≤ W.a := Real.rpow_le_rpow_of_exponent_le hN1 (by
    change -(p.s + p.u) ≤ -p.s
    linarith [p.u_pos])
  have ha2 : W.width 2 ≤ W.a := Real.rpow_le_rpow_of_exponent_le hN1 (by
    change -(p.s + p.v) ≤ -p.s
    linarith [p.v_pos])
  have hfine1 (γ : W.Coarse) : ((W.offsetBins γ 1 W.u).card : ℝ) ≤
      cfg.N k ^ ε * cfg.N k ^ (cfg.d * p.u) := by
    exact (W.fine_offset_count env.measurable hLμ hN rfl hD hXb cn.short.m_D
      cn.strip_drift cn.whole_key_strip hnull γ 1 p.u (hBsh 1) ha1 hOffsetH hwide1
      (out.radius p.s p.u (hξv.trans p.v_u.le)) (hn 1 (W.key γ) γ.1.1.2)
      (fun sp hs0 hs => env.caps sp hs0 (hs.trans (hdepth 1)))).trans (out.fine p.s p.u)
  have hfine2 (γ : W.Coarse) : ((W.offsetBins γ 2 W.v).card : ℝ) ≤
      cfg.N k ^ ε * cfg.N k ^ (cfg.d * p.v) := by
    exact (W.fine_offset_count env.measurable hLμ hN rfl hD hXb cn.short.m_D
      cn.strip_drift cn.whole_key_strip hnull γ 2 p.v (hBsh 2) ha2 hOffsetH hwide2
      (out.radius p.s p.v hξv) (hn 2 (W.key γ) γ.1.1.2)
      (fun sp hs0 hs => env.caps sp hs0 (hs.trans (hdepth 2)))).trans (out.fine p.s p.v)
  have hqP : W.q ≤ cfg.N k ^ σ * W.g := env.length.2.trans
    (mul_le_mul_of_nonneg_right hKN hg.le)
  have hcoeff (γ : W.Coarse) := W.prediction_coefficients_bound hv env.blocks P.L
    p.s_pos.le hKN le_rfl hqP hχ cn.short.chi_m γ
  have hfit1 : (cfg.N k ^ σ * W.width 1 + W.freezingError) / W.a + cfg.N k ^ (-p.M / 2) ≤
      cfg.N k ^ ε * cfg.N k ^ (-p.u) := by
    have hah : 0 < W.width 1 := Real.rpow_pos_of_pos hN _
    have hnum : cfg.N k ^ σ * W.width 1 + W.freezingError ≤ 2 * cfg.N k ^ σ * W.width 1 := by
      nlinarith [mul_le_mul_of_nonneg_right cn.input_one hah.le]
    exact (add_le_add (div_le_div_of_nonneg_right hnum ha.le) le_rfl).trans (out.fit p.s p.u hMu)
  have hfit2 : (cfg.N k ^ σ * W.width 2 + W.freezingError) / W.a + cfg.N k ^ (-p.M / 2) ≤
      cfg.N k ^ ε * cfg.N k ^ (-p.v) := by
    have hah : 0 < W.width 2 := Real.rpow_pos_of_pos hN _
    have hnum : cfg.N k ^ σ * W.width 2 + W.freezingError ≤ 2 * cfg.N k ^ σ * W.width 2 := by
      nlinarith [mul_le_mul_of_nonneg_right cn.input_one hah.le]
    exact (add_le_add (div_le_div_of_nonneg_right hnum ha.le) le_rfl).trans (out.fit p.s p.v hMv)
  exact W.comparedBlock_of_witnesses
    (C := cfg.N k ^ (20 * η) * (cfg.N k ^ ξ / (4 * cfg.N k ^ η)) ^ cfg.d) P rfl env.blocks env.measurable (hv.subpower.1 k)
    hN hχ cn.short.chi_m hle hpos hhor hkeys hgood
    (fun γ e => ((hcoeff γ).1 e).trans out.coefficients)
    (fun γ e => ((hcoeff γ).2 e).trans out.coefficients) hfit hfit1 hfit2
    (by positivity) out.coarse hcount hfine1 hfine2

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
