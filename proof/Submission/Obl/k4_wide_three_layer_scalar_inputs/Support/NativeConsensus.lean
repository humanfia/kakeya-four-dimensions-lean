import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.NativeIndex
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.BasicFinite

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

namespace ComparedBlock

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v M H θ : ℝ}
    (CB : ComparedBlock cfg k s u v (cfg.N k ^ (-M)) H) (E : NativeIndexScales)

/-- Fine-state pruning, actual coefficient agreement, and measured consensus on
the original compared law. Every loss is charged to its unchanged original block reference. -/
theorem native_consensus (hv : cfg.Valid)
    (num : NativeIndexBudget (cfg.N k) (cfg.K k) cfg.d cfg.S cfg.κ s u v M H CB.frame.q θ E)
    (hcap : CapsAt cfg k E.R) (hB : BlocksAt cfg k s E.R) (hBe : BlocksAt cfg k E.se E.R)
    (hnest : ∀ j : Fin (cfg.n k E.se), ∃ h : Fin (cfg.n k s), cfg.A k E.se j ⊆ cfg.A k s h ∧
      Data.I (cfg.T k E.se) (cfg.j k E.se j) ⊆ Data.I (cfg.T k s) (cfg.j k s h)) :
    Nonempty (NativeConsensusData CB E) := by
  classical
  have hN : 1 ≤ cfg.N k := by linarith [hv.scale k]
  have hNp : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hK : 1 ≤ cfg.K k := hv.subpower.1 k
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hH : 1 ≤ H := CB.H_one
  have hHp : 0 < H := zero_lt_one.trans_le hH
  obtain ⟨hb, hν, hπ, hμ, hρμ, -⟩ := hv.basic k
  letI : IsProbabilityMeasure (cfg.ν k) := hν
  letI : IsProbabilityMeasure (cfg.π k) := hπ
  letI : IsFiniteMeasure (cfg.μ k) := incidence_finite_of_valid hv k
  have hCBμ : CB.lam ≤ cfg.μ k := CB.lam_le.trans hρμ
  letI : IsFiniteMeasure CB.lam := isFiniteMeasure_of_le (cfg.μ k) hCBμ
  let P := nativeAgreeParams (cfg.N k) cfg.d u M E.B
  let W := ENNReal.ofReal CB.frame.q * cfg.ν k (cfg.A k s CB.i)
  let δp := ENNReal.ofReal (cfg.N k ^ (-E.ζ))
  let C₁ := ENNReal.ofReal (cfg.K k) / δp
  let w := 100 * H * (cfg.K k) ^ 2 * cfg.N k ^ (-u)
  let θm := nativeMatchThreshold (cfg.N k) cfg.d u
  let ρ2 := nativeReferenceDrift (cfg.N k) (cfg.K k) CB.frame.q M
  let ρN := nativeNearRadius (cfg.N k) (cfg.K k) CB.frame.q M E.B
  have hδ0 : δp ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hNp _))
  have hδtop : δp ≠ ⊤ := ENNReal.ofReal_ne_top
  have hC₁top : C₁ ≠ ⊤ := ENNReal.div_ne_top ENNReal.ofReal_ne_top hδ0
  have hq : 0 < CB.frame.q := by dsimp [frame, blockFrame]; positivity
  have hq₁ : CB.frame.q ≤ 1 := by
    dsimp [frame, blockFrame]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hg₁ : CB.frame.g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN
    (by nlinarith [hv.rate_pos, num.s_nonneg])
  have hχ : 0 < cfg.N k ^ (-M) := Real.rpow_pos_of_pos hNp _
  have hχ₁ : cfg.N k ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith [num.M_nonneg])
  have hdz : 0 < P.δz := Real.rpow_pos_of_pos hNp _
  have hdU : 0 < P.δU := Real.rpow_pos_of_pos hNp _
  have hdX : 0 < P.δX := Real.rpow_pos_of_pos hNp _
  have hdt : 0 < P.δt := hχ
  have hdt₁ : P.δt ≤ 1 := hχ₁
  have hdU₁ : P.δU ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith [num.u_nonneg])
  have hdzχ : P.δz ≤ cfg.N k ^ (-M) := Real.rpow_le_rpow_of_exponent_le hN (by linarith [num.M_B])
  have hdzU : P.δz ≤ P.δU := Real.rpow_le_rpow_of_exponent_le hN (by linarith [num.M_B, num.two_u_M])
  have hdtU : P.δt ≤ P.δU := Real.rpow_le_rpow_of_exponent_le hN (by linarith [num.two_u_M])
  have hsupp : ∀ᵐ p ∂CB.lam, p.1 ∈ cfg.B k s CB.i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s CB.i) := by
    filter_upwards [CB.lam_supp] with p hp
    exact ⟨hp.1, by rw [← blockFrame_interval CB.i CB.L]; exact hp.2⟩
  have hcoords := deepCoordinateBudgets_native_bound hv num.s_nonneg num.se_nonneg hB hBe
  have hc : ∀ e, deepCoordinateBudgets CB.frame.q CB.frame.g CB.frame.a
      (((2 : ℝ) ^ cfg.T k E.se)⁻¹) (cfg.N k ^ (-cfg.κ * E.se)) (cfg.N k ^ (-E.se))
      (cfg.K k) e ≤ P.δz := fun e => (hcoords e).trans num.deep_coordinates
  let qe := ((2 : ℝ) ^ cfg.T k E.se)⁻¹
  let ge := cfg.N k ^ (-cfg.κ * E.se)
  let ae := cfg.N k ^ (-E.se)
  obtain ⟨lam1, hle1, hloss1, hdom1⟩ := sigma_prune hν hK hNp hb hμ hB hBe hnest
    num.B_lo num.B_hi CB.i CB.L CB.hL CB.lam hCBμ hsupp hdz hdU hdX CB.frame rfl
    qe ge ae (cfg.K k) (14 * (cfg.K k) ^ 2 * qe ^ 2 + 2 * cfg.K k * qe * ge)
    rfl rfl rfl rfl rfl (hc 0) (hc 1) ((hc 2).trans hdzU) ((hc 3).trans hdzU) δp hδ0 hδtop
  have hle1μ : lam1 ≤ cfg.μ k := hle1.trans hCBμ
  letI : IsFiniteMeasure lam1 := isFiniteMeasure_of_le (cfg.μ k) hle1μ
  have hνA : cfg.ν k (cfg.A k s CB.i) ≠ 0 := true_assignment_ne_zero hB hNp hKp CB.i
  have hWpos : 0 < W := ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr hq, pos_iff_ne_zero.mpr hνA⟩
  have hWtop : W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hΓ : Nonempty CB.Γ := by
    have hpos : 0 < CB.lam univ :=
      (ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (inv_pos.mpr hHp), hWpos⟩).trans_le CB.lam_mass
    obtain ⟨p, -⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact ⟨CB.crs (CB.lab p.1)⟩
  have hθ := agreement_threshold_bounds hN hv.dimension_lt_one.le num.u_nonneg
  have hgap := agreement_gap_bound hN (zero_le_one.trans hH) hdzU hdtU num.reference_drift num.gap
  have hρ20 : 0 ≤ ρ2 := by dsimp [ρ2, nativeReferenceDrift]; positivity
  have hw := agreement_width_bound hN hK hH num.u_nonneg hdt.le hdz.le hdU.le hdX.le hρ20
    hdtU hdzU le_rfl le_rfl num.reference_drift
  have hρN := agreement_near_radius_bound hK hq.le hq₁ hχ.le hχ₁ hdz.le hdzχ
  obtain ⟨center, Hc, hHc, hrel, hhalf, hmass1⟩ := CB.agreement_final P hcap hB hNp hK hb CB.hL
    hχ hH hπ hdt (hdt₁.trans (by norm_num)) hdz hdU hdX (by dsimp [P, nativeAgreeParams]; positivity)
    (ρ2 := ρ2) (ρN := ρN) (w := w) le_rfl le_rfl hgap hw (by dsimp [w]; positivity)
    num.r_lo num.r_hi num.sp_lo num.sp_hi num.B_lo num.B_hi num.window CB.L_bd hg₁
    hdzχ (hχ₁.trans hK) num.match_mesh_time num.match_mesh_chart num.match_mesh_transverse
    num.match_mesh_width num.match_lip hθ.1 hθ.2
    (fun sr _ c _ γ _ hocc => CB.occupied_slope_bound P hB hNp hK hχ num.chart_length hχ₁
      hdt hdt₁ hdU.le hdU₁ sr c γ hocc)
    lam1 hle1 hle1μ C₁ hC₁top hΓ hdom1
  let lam2 := lam1.restrict Hc
  have hC₁eq : C₁ = ENNReal.ofReal (cfg.K k * cfg.N k ^ E.ζ) := by
    dsimp only [C₁, δp]
    rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hNp _)]
    congr 1
    rw [div_eq_mul_inv, ← Real.rpow_neg hNp.le, neg_neg]
  have hC₁real : C₁.toReal = cfg.K k * cfg.N k ^ E.ζ := by
    rw [hC₁eq, ENNReal.toReal_ofReal (by positivity)]
  have hlen : 0 ≤ nativeMatchFactor (cfg.N k) (cfg.K k) H cfg.d u := by
    dsimp [nativeMatchFactor, nativeMatchThreshold, nativeTau]
    positivity
  have hLoss := CB.agreeLoss_toReal_le_original_reference P hB hNp hK hv.dimension_lt_one.le
    hχ hχ₁ num.chart_length rfl hdU num.source_width
    (r := E.r) (sp := E.sp) (vp := E.B) (θm := θm) (w := w) (LipU := 24 * H * cfg.K k)
    hρN num.window C₁ hC₁top hlen
  have hWreal : W.toReal = CB.frame.q * (cfg.ν k (cfg.A k s CB.i)).toReal := by
    dsimp only [W]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le]
  rw [hC₁real, ← hWreal] at hLoss
  have hLoss' : (CB.agreeLoss P C₁ E.r E.sp E.B θm w (24 * H * cfg.K k) ρN).toReal ≤
      (cfg.K k * cfg.N k ^ E.ζ) * cfg.N k ^ (-E.β) *
        (100000000 * (cfg.K k) ^ 4 * H ^ 4) * W.toReal := by
    refine hLoss.trans ?_
    gcongr
    exact num.match_factor
  have hpruneR : CB.lam.real univ ≤ lam1.real univ + 81 * cfg.N k ^ (-E.ζ) * W.toReal := by
    have h81top : δp * ((81 : ℝ≥0∞) * W) ≠ ⊤ :=
      ENNReal.mul_ne_top hδtop (ENNReal.mul_ne_top (by norm_num) hWtop)
    have hfin : lam1 univ + δp * ((81 : ℝ≥0∞) * W) ≠ ⊤ := by finiteness
    have hh := ENNReal.toReal_mono hfin hloss1
    change (CB.lam univ).toReal ≤ (lam1 univ + δp * ((81 : ℝ≥0∞) * W)).toReal at hh
    simp only [ENNReal.toReal_add (measure_ne_top lam1 univ) h81top,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hh
    have hdreal : δp.toReal = cfg.N k ^ (-E.ζ) := ENNReal.toReal_ofReal (Real.rpow_nonneg hNp.le _)
    rw [hdreal] at hh
    simpa only [Measure.real, mul_assoc, mul_left_comm] using hh
  have hfloorR : H⁻¹ * W.toReal ≤ CB.lam.real univ := by
    have hf : ENNReal.ofReal H⁻¹ * W ≤ CB.lam univ := CB.lam_mass
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (zero_le_one.trans hH))]
      using ENNReal.toReal_mono (measure_ne_top _ _) hf
  have hkeptR : cfg.N k ^ (-E.η) * W.toReal ≤ lam2.real univ := by
    have hmR := consensus_restrict_real_mass lam1 Hc hmass1
    change lam1.real univ ≤ (lam1.restrict Hc).real univ +
      2 * (CB.agreeLoss P C₁ E.r E.sp E.B θm w (24 * H * cfg.K k) ρN).toReal at hmR
    have hbR := mul_le_mul_of_nonneg_right num.mass (ENNReal.toReal_nonneg (a := W))
    dsimp only [lam2]
    nlinarith only [hfloorR, hpruneR, hmR, hLoss', hbR]
  have hmass2 : ENNReal.ofReal (cfg.N k ^ (-E.η)) * W ≤ lam2 univ := by
    apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWtop)
      (measure_ne_top _ _)).mp
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hNp.le _)] using hkeptR
  have h2C : 2 * C₁ ≤ ENNReal.ofReal (cfg.N k ^ E.η) := by
    calc
      _ = ENNReal.ofReal (2 * (cfg.K k * cfg.N k ^ E.ζ)) := by
        rw [hC₁eq, ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using num.conditional)
  have hstate := consensus_restrict_palette lam1 (CB.sig P) (CB.measurable_sig P hb)
    (fun p => vbin (cfg.N k ^ (-E.B)) (cfg.b k p.1 3))
    (paletteBins (cfg.π k) (cfg.N k ^ (-E.B))) C₁ Hc hhalf hdom1
  refine ⟨{
    lam := lam2
    center := center
    le := (Measure.restrict_le_self : lam1.restrict Hc ≤ lam1).trans hle1
    mass := hmass2
    agree := ?_
    state := ?_ }⟩
  · filter_upwards [ae_restrict_mem hHc] with p hp
    exact hrel p hp
  · intro Q V
    exact (hstate Q V).trans (mul_le_mul' (mul_le_mul' h2C le_rfl) le_rfl)

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
