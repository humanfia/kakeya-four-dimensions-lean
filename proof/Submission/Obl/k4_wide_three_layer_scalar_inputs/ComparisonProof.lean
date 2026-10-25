import Submission.Obl.k4_wide_three_layer_scalar_inputs.ComparisonTarget
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ComparedIndex
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortRetention
import Submission.Obl.k4_wide_three_layer_scalar_inputs.AffinePrefix
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ProjectedRegularity

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory Set Filter
open Inherited.Native Inherited.Core

noncomputable section

/-- Matching produces the complete compared original block from the
supplied three layers, at every output loss and at their fixed exponents. -/
theorem comparedPreparation_of_match (hM : Match) : ComparedPreparation := by
  classical
  intro α _ cfg hv buffer hb p hProjected ε hε
  obtain ⟨ηmatch, hmatch, R₀, -, hPC⟩ := match_comparison_constants (α := α) hM
    hv.dimension_nonneg hv.dimension_lt_one
  have hvpos : 0 < p.v := p.v_pos
  have hs₀pos : 0 < p.s₀ := p.s₀_pos
  let ξ := min (p.v / 2) (ε / 100)
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξv : ξ ≤ p.v := by have h := min_le_left (p.v / 2) (ε / 100); dsimp [ξ]; linarith [p.v_pos]
  have hξε : ξ ≤ ε / 100 := min_le_right _ _
  obtain ⟨η₀, hη₀, hnum⟩ := eventually_comparisonNumerics hv.scale hv.scale_limit
    hv.dimension_nonneg hv.dimension_lt_one hv.rate_pos hv.rate_le_one hb p hξ hmatch (R₀ := R₀)
  let η := min η₀ (ε / 1000) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hη₀' : η ≤ η₀ := by
    have hh := min_le_left η₀ (ε / 1000)
    dsimp [η]
    linarith
  have hηε : η ≤ ε / 1000 := by
    have hh := min_le_right η₀ (ε / 1000)
    dsimp [η]
    linarith
  let σ := min (η / 100) (p.s₀ / 100) / 2
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hση : 100 * σ ≤ η := by
    have hh := min_le_left (η / 100) (p.s₀ / 100)
    dsimp [σ]
    linarith
  have hσs₀ : σ ≤ p.s₀ / 20 := by
    have hh := min_le_right (η / 100) (p.s₀ / 100)
    dsimp [σ]
    linarith [p.s₀_pos]
  have hchart : 2 * σ ≤ p.s₀ := by linarith [p.s₀_pos]
  have hgap : σ + 20 * η + ξ < ε := by linarith
  have hηε' : η ≤ ε := by linarith
  have hsp : p.s < 3 * p.s₀ / 2 := by linarith [p.su_s₀, p.u_pos]
  have hM100 : 100 * p.s₀ < p.M :=
    (mul_lt_mul_of_pos_right hb p.s₀_pos).trans p.M_lower
  obtain ⟨Rcap, -, henv⟩ := eventually_comparison_environment hv hb p
  filter_upwards [henv, hnum η hη hη₀' σ hσ hση,
    eventually_comparisonOutputs hv.scale hv.scale_limit hv.dimension_nonneg hv.dimension_lt_one
      hσ hη hξ hση hgap (M := p.M),
    hv.subpower.2 σ hσ,
    Data.eventually_projectedAt_rebound hv p.s₀_pos.le hProjected σ hσ,
    eventually_exists_affine_prefix hv p.s₀_pos p.s₀_s hsp,
    ShortWitnesses.Context.eventually_prediction_fits cfg hv p.s₀_pos hsp hM100 hσ hchart]
      with k env hcn hout hKN hlayers hprefix hprediction
  letI : IsProbabilityMeasure (cfg.ν k) := env.prior_prob
  letI : IsProbabilityMeasure (cfg.π k) := env.palette_prob
  letI : IsFiniteMeasure (cfg.μ k) := env.finite
  have hN : 0 < cfg.N k := by linarith [hv.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [hv.scale k]
  have hK : 1 ≤ cfg.K k := hv.subpower.1 k
  have cn := hcn (cfg.K k) (slotLen cfg.comparisonData k p.s) hK hKN env.length.1 env.length.2
  have out := hout (cfg.K k) hK hKN
  obtain ⟨L⟩ := hlayers.comparedLayers
  have hnull : L.ρs (horizSet (cfg.b k) (cfg.N k ^ (-cfg.e₀)))ᶜ = 0 :=
    ae_iff.mp (ae_mono (L.le_rho.trans env.rho_le) env.horizontal)
  obtain ⟨i, lam, hle, -, hsupp, hmass, hpos, hgood⟩ := exists_short_retained_block p L
    (hv.scale k) hK env.measurable env.rho_le env.blocks hPC cn env.caps hnull
  have hmassOut : ENNReal.ofReal ((cfg.N k ^ ε)⁻¹) *
      (ENNReal.ofReal (((2 : ℝ) ^ cfg.T k p.s)⁻¹) * cfg.ν k (cfg.A k p.s i)) ≤ lam univ := by
    apply le_trans _ hmass
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.rpow_neg hN.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  obtain ⟨P, hi, hPlam, -, hLraw⟩ := hprefix σ ε hσ.le hσs₀ hε.le hKN
    _ Rcap _ _ p.u _ env.blocks L i lam hle hpos hsupp hmassOut
  let W := L.shortContext P.i η ξ
  have hleP : P.lam ≤ L.ρs := by simpa only [hPlam] using hle
  have hposP : 0 < P.lam univ := by simpa only [hPlam] using hpos
  have hgoodP : ∀ᵐ z ∂P.lam, z ∉ W.exception := by
    change ∀ᵐ z ∂P.lam, z ∉ L.shortException η ξ
    simpa only [hPlam] using hgood
  have hCoeffExp : 4 * cfg.κ * p.s₀ + σ ≤ 10 * p.s₀ := by
    have hh : cfg.κ * p.s₀ ≤ p.s₀ := mul_le_of_le_one_left p.s₀_pos.le hv.rate_le_one
    linarith [p.s₀_pos]
  have hcoeff : ∀ (γ : W.Coarse) e,
      |(W.layers.G 0 (W.coarseIndex γ)).coeff e| ≤ cfg.N k ^ (10 * p.s₀) := by
    intro γ e
    exact ((L.piece 0 (W.coarseIndex γ)).2.2.2.1 e).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hCoeffExp)
  have hm : 0 < W.m := mul_pos (slotLen_pos cfg.comparisonData k p.s)
    (Real.rpow_pos_of_pos hN _)
  have hsmall : W.q * (W.ζ + W.χ) ≤ W.m / 2 := by
    have hh := mul_le_mul_of_nonneg_left cn.short.jitter_quarter hm.le
    have hs := cn.short.interval_drift
    change W.q * (W.ζ + W.χ) ≤ W.m * cfg.N k ^ (-p.M / 4) at hs
    linarith
  have hfit : W.PredictionFits P.L (cfg.N k ^ (-p.M / 2)) :=
    hprediction W rfl rfl rfl rfl Rcap (cfg.N k ^ σ) env.blocks P.L P.hL hKN le_rfl le_rfl
      (Real.rpow_pos_of_pos hN _) cn.short.m_D cn.strip_drift hsmall hcoeff (hLraw 2) (hLraw 3)
  exact compared_index_of_prefix hv hb p L env cn out hKN hξv P hleP hposP hgoodP hfit

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
