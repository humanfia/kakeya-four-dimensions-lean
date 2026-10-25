import Submission.Obl.k4_wide_three_layer_scalar_inputs.NativeGlobal
import Submission.Obl.k4_wide_three_layer_scalar_inputs.NativeCalibration
import Submission.Obl.k4_wide_three_layer_scalar_inputs.NativeEnvironment
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ComparisonProof
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.NativeFrameBounds
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.NativeIndexProof
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.NativeConsensus

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory Set Filter
open Support

noncomputable section

/-- Matching supplies the compared original block, and the local common
field and original caps supply the frozen native extraction at all losses. -/
theorem nativePreparation : NativePreparation := by
  intro hCF _hRow hMatch α _ cfg hv hProjected
  obtain ⟨C₀, hC, hField⟩ := Field.commonField_at hCF cfg.S hv.palette_pos
  let buffer := 10000 * C₀ * (1 + cfg.κ⁻¹)
  have hb : 100 < buffer := by
    have hi := inv_pos.mpr hv.rate_pos
    dsimp [buffer]
    nlinarith
  obtain ⟨p, hp⟩ := Data.projected_parameters hProjected hb
  let τ := nativeTau cfg.d p.u
  let B := C₀ * (10 * p.M + τ)
  let se := 100 * B / cfg.κ + 100 * p.M
  have hhor := native_horizon_choices hC hv.dimension_nonneg hv.dimension_lt_one
    hv.rate_pos hv.rate_le_one p
  obtain ⟨hτ, hvτ, -, hM, hm, hvm, hκsm, hMm, hsvU, hJ, hsse, hseU, -, -⟩ := hhor
  change 0 < τ at hτ
  change 2 * p.v < τ at hvτ
  have hsse' : p.s < se := by
    simpa only [se, B, τ, nativeTau, mul_assoc] using hsse
  have hseU' : se < cfg.U := by
    simpa only [se, B, τ, nativeTau, mul_assoc] using hseU
  refine ⟨p.s, p.v, 2 * p.M, p.M, 17 + 2 * p.s,
    p.s_pos, p.v_pos, hvm, hκsm, hM, hMm, hsvU, hJ, ?_⟩
  intro θ hθ
  obtain ⟨εF, hεF, hεθ, hετ, -⟩ := native_field_loss_choice hθ (by linarith : p.v < τ)
  obtain ⟨η, hη, hηε, N₀, -, hF⟩ := hField (10 * p.M) τ (by positivity) hτ εF hεF
  obtain ⟨σ, ζ, R, hσ, -, hR, hRs, hnum⟩ := eventually_native_index_budget hv hC p
    hθ hεF hεθ hετ hη hηε
  have henv := eventually_native_environment hv hR hRs hsse' hseU'.le
  have hCompared := comparedPreparation_of_match hMatch α cfg hv buffer hb p hp σ hσ
  filter_upwards [hCompared, hnum, henv, hv.scale_limit.eventually_ge_atTop N₀]
    with k hCB hbudget env hlarge
  obtain ⟨CB⟩ := hCB
  let E := calibratedNativeScales (cfg.N k) cfg.d cfg.κ p.s p.u p.M C₀ εF η ζ σ R
  have hN : 0 < cfg.N k := by linarith [hv.scale k]
  have hq₁ : CB.frame.q ≤ 1 := by
    dsimp [ComparedBlock.frame, blockFrame]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hlen := Submission.Obl.k4_horizontal_supercritical_three_projections.block_length_bounds
    hN (hv.subpower.1 k) env.blocks.T_lo env.blocks.T_hi
  simp only [zpow_neg, zpow_natCast] at hlen
  have hqlo : cfg.N k ^ (-cfg.κ * p.s) / cfg.K k ≤ CB.frame.q := by
    simpa only [ComparedBlock.frame, blockFrame, neg_mul] using hlen.1
  have num : NativeIndexBudget (cfg.N k) (cfg.K k) cfg.d cfg.S cfg.κ
      p.s p.u p.v p.M (cfg.N k ^ σ) CB.frame.q θ E := hbudget CB.frame.q hqlo hq₁
  let _ : IsFiniteMeasure (cfg.μ k) := hv.native_incidence_finite k
  obtain ⟨F⟩ := CB.native_consensus E hv num env.caps env.blocks env.deep_blocks env.nesting
  exact ComparedBlock.native_index_after_consensus hv CB E num (hF (cfg.N k) hlarge)
    env.caps env.blocks env.deep_blocks env.nesting F

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
