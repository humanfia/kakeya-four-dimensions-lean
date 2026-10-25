import Submission.Obl.k4_wide_three_layer_scalar_inputs.NativeEnvironment
import Submission.Obl.k4_wide_three_layer_scalar_inputs.NativeLossChoices
import Submission.Obl.k4_wide_three_layer_scalar_inputs.NativeMassBudgets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.NativeScaleMargins
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Field.RecoveryBudgets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.HiddenWindow
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.NativeRawBudgets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.NativeIndex

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory Set Filter
open Support

noncomputable section

/-- The output depths are fixed before all losses. Only the cap range,
small losses and exact hidden-window exponent vary in the construction. -/
def calibratedNativeScales (N d κ s u M C₀ εF η ζ σ R : ℝ) : NativeIndexScales where
  R := R
  se := 100 * (C₀ * (10 * M + nativeTau d u)) / κ + 100 * M
  m := 2 * M
  J := 17 + 2 * s
  C₀ := C₀
  A := 10 * M
  B := C₀ * (10 * M + nativeTau d u)
  εF := εF
  η := η
  ζ := ζ
  β := (1 - d) * u / 16
  r := 10 * (C₀ * (10 * M + nativeTau d u))
  sp := hiddenWindowExponent N (N ^ σ) s u
  scell := s - 2 * σ
  v₀ := min ((C₀ * (10 * M + nativeTau d u)) / 2) (η / 2)

set_option maxHeartbeats 2000000 in
/-- The buffered projected depths and independent subpower choices pay
all fifty-five numerical premises of the actual native index theorem. -/
theorem eventually_native_index_budget {α : Type} [MeasurableSpace α]
    {cfg : Data α} (hv : cfg.Valid) {C₀ : ℝ} (hC : 100 < C₀)
    (p : Parameters cfg.d cfg.κ cfg.U cfg.e₀ (10000 * C₀ * (1 + cfg.κ⁻¹)))
    {θ εF η : ℝ} (hθ : 0 < θ) (hεF : 0 < εF) (hεθ : εF ≤ θ / 100)
    (hετ : εF ≤ (nativeTau cfg.d p.u - p.v) / 100)
    (hη : 0 < η) (hηε : η ≤ εF) :
    ∃ σ ζ R : ℝ, 0 < σ ∧ 0 < ζ ∧ 1 < R ∧ R⁻¹ ≤ p.s ∧
      ∀ᶠ k in atTop, ∀ q : ℝ,
        cfg.N k ^ (-cfg.κ * p.s) / cfg.K k ≤ q → q ≤ 1 →
        NativeIndexBudget (cfg.N k) (cfg.K k) cfg.d cfg.S cfg.κ
          p.s p.u p.v p.M (cfg.N k ^ σ) q θ
          (calibratedNativeScales (cfg.N k) cfg.d cfg.κ p.s p.u p.M C₀ εF η ζ σ R) := by
  let τ := nativeTau cfg.d p.u
  let B := C₀ * (10 * p.M + τ)
  let se := 100 * B / cfg.κ + 100 * p.M
  let β := (1 - cfg.d) * p.u / 16
  have hτ : 0 < τ := div_pos (mul_pos (sub_pos.mpr hv.dimension_lt_one) p.u_pos) (by norm_num)
  have hβ : 0 < β := div_pos (mul_pos (sub_pos.mpr hv.dimension_lt_one) p.u_pos) (by norm_num)
  have hb : 100 < 10000 * C₀ * (1 + cfg.κ⁻¹) := by
    have hi := inv_pos.mpr hv.rate_pos
    nlinarith
  have hM : 0 < p.M := p.M_pos (by linarith)
  have hκ : 0 < cfg.κ := hv.rate_pos
  obtain ⟨ζ, σ, hζ, hσ, hζη, hζβ, hσζ, hσs, hσu, hσM, hσθ, hσ1,
    hσζ', hcond, hcap, hag, htable⟩ :=
    native_subpower_choices hη hβ p.s_pos p.u_pos hM hθ hεθ
  have hετ' : εF ≤ (1 - cfg.d) * p.u / 200 := by
    dsimp [τ, nativeTau] at hετ ⊢
    linarith [p.v_pos]
  obtain ⟨-, hsu, hB, hBp, hMB, huB, hcell0, hBτ, hMτ, hMτ', hBv, hout,
    hdeep, hcorr⟩ := native_scale_margins hC hv.dimension_nonneg hv.dimension_lt_one
      hv.rate_pos p hσ hσs hσu hσM hετ'
  change 10 * p.M ≤ B at hB
  change 0 < B at hBp
  change p.M ≤ B at hMB
  change 2 * p.u ≤ B at huB
  change σ + τ ≤ B at hBτ
  change 2 * σ + p.s + τ ≤ p.M at hMτ
  change σ + τ ≤ p.M at hMτ'
  change σ + p.v ≤ B at hBv
  change 7 * σ + 2 * p.s - cfg.κ * se < -B at hdeep
  change εF + 8 * σ + 2 * p.s - cfg.κ * se < -p.v at hcorr
  have hεv : εF + p.v ≤ τ := by linarith only [hετ, hεF]
  have hvτ : p.v ≤ τ := by linarith only [hεv, hεF]
  have hση : σ < η := by linarith only [hcond, hζ]
  have hcoef : 2 * σ < η := by linarith only [hcap, hσ]
  have hmatch : 64 * σ < (1 - cfg.d) * p.u := by
    change ζ ≤ ((1 - cfg.d) * p.u / 16) / 100 at hζβ
    linarith
  have hgap : σ - 2 * p.u < -τ := by
    have hh : τ ≤ p.u / 2 := by
      dsimp [τ, nativeTau]
      nlinarith [mul_nonneg hv.dimension_nonneg p.u_pos.le]
    linarith
  let v₀ := min (B / 2) (η / 2)
  have hv₀ : 0 < v₀ := lt_min (by positivity) (by positivity)
  have hv₀B : v₀ ≤ B := (min_le_left _ _).trans (by linarith)
  have hv₀η : v₀ * cfg.S ≤ η := by
    have hh : v₀ ≤ η / 2 := min_le_right _ _
    have hm := mul_le_of_le_one_right hv₀.le hv.palette_le_one
    linarith
  obtain ⟨R, hR, hRs, hsR, hrlo, hrhi, hBlo, hBhi, hv₀lo, -, hsuR⟩ :=
    exists_native_cap_range p.s_pos p.u_pos.le hBp hv₀
  refine ⟨σ, ζ, R, hσ, hζ, hR, hRs, ?_⟩
  filter_upwards [hv.subpower.2 σ hσ,
    hv.scale_limit.eventually (eventually_native_raw_budgets p.s_pos.le p.u_pos.le hM hsu hB hσ (by linarith)),
    hv.scale_limit.eventually (Field.eventually_field_native_budgets hσ hη hv.dimension_lt_one.le
      hcoef hcap hBτ hMτ hMτ' hεv hvτ hBv hout),
    hv.scale_limit.eventually (eventually_native_mass_budgets hσζ' hcond hag hση hεF),
    hv.scale_limit.eventually (eventually_agreement_matching_factor hv.dimension_lt_one.le p.u_pos.le hσ.le hmatch),
    hv.scale_limit.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 10 hgap),
    hv.scale_limit.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 100 hdeep),
    hv.scale_limit.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 1600 hcorr),
    hv.scale_limit.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 3 (a := 0) hσ),
    hv.scale_limit.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 4 hση),
    hv.scale_limit.eventually (eventually_residual_extraction_count (κ := σ) (ξ := 4 * σ)
      (η := εF) (θ := θ) (by linarith))]
    with k hKN hraw hfield hmass hmatching hgapk hdeepk hcorrk hthree hfour hcount
  let N := cfg.N k
  let K := cfg.K k
  let H := N ^ σ
  have hN : 1 ≤ N := by dsimp [N]; linarith [hv.scale k]
  have hN' : 1 < N := by dsimp [N]; linarith [hv.scale k]
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hK : 1 ≤ K := hv.subpower.1 k
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hH : 1 ≤ H := Real.one_le_rpow hN hσ.le
  have hHN : H ≤ N ^ σ := le_rfl
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  change K ≤ N ^ σ at hKN
  simp only [Real.rpow_zero, mul_one] at hthree
  intro q hqlo hq1
  have hκs : cfg.κ * p.s ≤ p.s := mul_le_of_le_one_left p.s_pos.le hv.rate_le_one
  have hqlo' : N ^ (-p.s) / K ≤ q := by
    exact (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hκs])) hK0).trans hqlo
  have raw := hraw K H q cfg.κ hK hH hKN hHN hv.rate_le_one hqlo hq1
  obtain ⟨hfieldK, hfieldH, hfieldfit, hcellbudget, hrecovery, hheight, hsmall⟩ :=
    hfield K H q hK hH hKN hHN hqlo'
  obtain ⟨hprune, hagree, hconditional, hmassfloor, hlarge⟩ := hmass K H hK0 hH0 hKN hHN
  obtain ⟨hsp_lower, hsp_upper, hwindow⟩ := hiddenWindowExponent_bounds (s := p.s) (u := p.u) hN' hH hHN hthree
  have hsp0 : 0 ≤ hiddenWindowExponent N H p.s p.u := by linarith only [hsp_lower, hσs, p.s_pos, p.u_pos]
  have hspR : hiddenWindowExponent N H p.s p.u ≤ R := hsp_upper.trans hsuR
  have hmass' : N ^ (-η) + 81 * N ^ (-ζ) +
      2 * (K * N ^ ζ) * N ^ (-β) * (100000000 * K ^ 4 * H ^ 4) ≤ H⁻¹ := by
    change N ^ (-η) + 81 * N ^ (-ζ) +
      2 * (K * N ^ ζ) * N ^ (-β) * (100000000 * K ^ 4 * H ^ 4) ≤ (N ^ σ)⁻¹
    rw [← Real.rpow_neg hNp.le]
    linarith only [hprune, hagree, hmassfloor, Real.rpow_nonneg hNp.le (-σ)]
  have hgap' : 10 * H * N ^ (-2 * p.u) ≤ N ^ (-τ) := by
    calc _ = 10 * N ^ (σ - 2 * p.u) := by
          dsimp [H]
          rw [mul_assoc, ← Real.rpow_add hNp]
          congr 2
          ring
      _ ≤ _ := hgapk
  have hdeep' : 100 * K ^ 7 * N ^ (2 * p.s - cfg.κ * se) ≤ N ^ (-B) := by
    calc _ ≤ 100 * (N ^ σ) ^ 7 * N ^ (2 * p.s - cfg.κ * se) := by gcongr
      _ = 100 * N ^ (7 * σ + 2 * p.s - cfg.κ * se) := by
          rw [← Real.rpow_mul_natCast hNp.le, mul_assoc, ← Real.rpow_add hNp]
          congr 1
          push_cast
          ring
      _ ≤ _ := hdeepk
  have hcorr' : 1600 * N ^ εF * K ^ 8 * N ^ (2 * p.s - cfg.κ * se) ≤ N ^ (-p.v) := by
    calc _ ≤ 1600 * N ^ εF * (N ^ σ) ^ 8 * N ^ (2 * p.s - cfg.κ * se) := by gcongr
      _ = 1600 * N ^ (εF + 8 * σ + 2 * p.s - cfg.κ * se) := by
          rw [← Real.rpow_mul_natCast hNp.le, mul_assoc 1600,
            ← Real.rpow_add hNp, mul_assoc, ← Real.rpow_add hNp]
          congr 1
          push_cast
          ring
      _ ≤ _ := hcorrk
  have hL : H * N ^ (2 * p.s) ≤ N ^ (17 + 2 * p.s) := by
    change N ^ σ * N ^ (2 * p.s) ≤ _
    rw [← Real.rpow_add hNp]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hσ1])
  have hKθ : K ≤ N ^ θ := hKN.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hσθ, hθ]))
  refine {
    s_nonneg := p.s_pos.le
    se_nonneg := by change 0 ≤ se; dsimp [se]; positivity
    εF_nonneg := hεF.le
    u_nonneg := p.u_pos.le
    M_nonneg := hM.le
    m_nonneg := by change 0 ≤ 2 * p.M; positivity
    M_m := by change p.M ≤ 2 * p.M; linarith
    M_A := by change p.M ≤ 10 * p.M; linarith
    M_B := hMB
    two_u_M := by linarith [p.s_pos]
    m_B := by change 2 * p.M ≤ B; linarith
    field_mesh := rfl
    chart_length := raw.chart_q
    source_width := raw.source_width
    reference_drift := raw.rho2
    gap := hgap'
    match_factor := ?_
    mass := hmass'
    conditional := by
      change 2 * K * N ^ ζ ≤ N ^ η
      simpa only [mul_assoc] using hconditional
    r_lo := hrlo
    r_hi := hrhi
    sp_lo := hsp0
    sp_hi := hspR
    B_lo := hBlo
    B_hi := hBhi
    window := hwindow
    match_mesh_time := raw.agree_time
    match_mesh_chart := raw.agree_chart
    match_mesh_transverse := raw.agree_width
    match_mesh_width := raw.agree_base
    match_lip := raw.agree_lip.trans (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hsp_upper))
    field_K := hfieldK
    field_H := hfieldH
    field_fit := hfieldfit
    field_base_width := raw.field_g
    cell_lo := hcell0
    cell_hi := (by change p.s - 2 * σ ≤ R; linarith only [hsR, hσ])
    R_one := hR.le
    cell_hidden_width := raw.field_fit
    cell_mesh := raw.field_mesh
    cell_lip := raw.field_lip
    cell_budget := hcellbudget
    frost_v₀_pos := hv₀
    frost_v₀_B := hv₀B
    frost_dimension := hv₀η
    frost_K := (mul_le_mul_of_nonneg_left hKN (by norm_num)).trans hfour
    frost_lo := hv₀lo
    deep_coordinates := hdeep'
    deep_corrected := hcorr'
    recovery := hrecovery
    output_small := hsmall
    output_large := hlarge
    output_loss := by change 2 * εF ≤ θ; linarith only [hεθ, hθ]
    output_C := by change εF ≤ θ; linarith only [hεθ, hθ]
    output_count := hcount K (8 * H * K ^ 2) hK0 (by positivity) hKN hheight
    output_L := hL
    output_K := hKθ }
  change nativeMatchFactor N K H cfg.d p.u ≤ N ^ (-β)
  simpa only [nativeMatchFactor, nativeMatchThreshold, nativeTau, β, neg_div, N, K, H]
    using hmatching K H (N ^ (-2 * p.u)) hK hKN hH hHN (by positivity) le_rfl

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
