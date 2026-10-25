import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Kernels

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface
open Submission.Lib.K4QuadraticSheets

set_option maxHeartbeats 2000000 in
/-- The single-sample analytic construction under the weaker path interface.
All discarded masses, caps and floors use the original world priors. -/
theorem preparedSampleCore : PreparedSampleCore := by
  classical
  intro hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  obtain ⟨Cs, hCs, hsheets⟩ := exists_packet_sheet_for_lines hsheets
  obtain ⟨Cdisc, hCdisc, hdisc⟩ := exists_packet_discriminant_bound
  obtain ⟨params, hGR⟩ := exists_group_recovery hgraph hremez 2 d₁ hd₁ hd₁1
  let εG := matchExp params.epsilon d₁
  let θ := thetaOf εG
  let Λ := expMult Cs 6 params.remezExponent
  let ϖ := varpiOf εG κ₁ θ Λ
  let Kd := discriminantConstant Cdisc
  have hKd : 0 ≤ Kd := by dsimp [Kd, discriminantConstant]; positivity
  have hεG : 0 < εG := matchExp_pos params.epsilon_pos hd₁1
  have hεGp : εG ≤ params.epsilon := (matchExp_le params.epsilon hd₁1.le).1
  have hdεG : d₁ + εG ≤ 1 := (matchExp_le params.epsilon hd₁1.le).2.1
  have hεG2 : εG ≤ 1 / 2 := (matchExp_le params.epsilon hd₁1.le).2.2
  have hθ : 0 < θ := thetaOf_pos hεG
  have hθ4 : θ ≤ 1 / 4 := thetaOf_le_quarter _
  have hθε : θ ≤ εG / 4 := thetaOf_le _
  have hΛ : 0 < Λ := expMult_pos (by norm_num) (by linarith [params.remezExponent_one])
  have hϖ : 0 < ϖ := varpiOf_pos hεG hκ₁ hθ hΛ
  refine ⟨θ, ϖ, hθ, hθ4, hϖ, ?_⟩
  intro ρ hρ hρϖ _hρ4 _hdρ L m s gain δ₀ hL _hgrid hgain _hgain1 hδ₀ hδρ
    Mp Dp Mg Dg Mpr Dpr
  let sE := scaleExp Kd 6 ϖ gain L
  let tE := timeExp κ₁ θ gain L
  let Mc := coreExp Mg Mpr Kd 6 ϖ gain L κ₁ θ
  refine ⟨Mc, ?_⟩
  intro β ε₀ σ₀ τ hβ hβ1 hε₀ hε₀β hσ₀ hσ₀β hτ hsum
  let J : ℝ := ∑ a : GroupJetIndex params, params.upper a.2.val
  let Clist : ℕ := 7 ^ Fintype.card (GroupJetIndex params)
  let N₀ := max
    (sampleN0 Kd 6 params.remezScale params.remezExponent Cs κ₁ θ gain L εG β τ
      params.radius J params.lower ((2 : ℝ) ^ (23 : ℕ)) Clist)
    ((101 * (Clist : ℝ) + 1) ^ (1 / (β / 4)))
  have hN₀2 : 2 ≤ N₀ := by
    exact (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨N₀, hN₀2, ?_⟩
  intro Nk hNk W ω ν E B f hlin ε σ hε hεbound hσ hσbound
    r T nw κ C lev par γ j c u Q R A F lst hpath i h n old R' A' V q hsi
  have hNk2 : 2 ≤ Nk := hN₀2.trans hNk
  have hNk1 : 1 ≤ Nk := by linarith
  have hNk0 : 0 < Nk := by linarith
  obtain ⟨_, hNtime, hNwidth, hNremez, hNthr1, hNthr2, hNcount, hNradius,
    hNmatch, hNpair, hNlight, hNfinal, _⟩ := sampleN0_spec
      (show sampleN0 Kd 6 params.remezScale params.remezExponent Cs κ₁ θ gain L εG β τ
        params.radius J params.lower ((2 : ℝ) ^ (23 : ℕ)) Clist ≤ Nk from
          (le_max_left _ _).trans hNk)
  have hNlist : (101 * (Clist : ℝ) + 1) ^ (1 / (β / 4)) ≤ Nk :=
    (le_max_right _ _).trans hNk
  have hsum' : ε + σ + τ ≤ ϖ * gain * L := by linarith
  have hbud := slack_budget hΛ hρϖ hgain hL hsum'
  let S := slackTot ρ gain L ε σ τ
  let U := Nk ^ greedySlack ρ gain L ε
  let Abound := sheetScale Kd 6 Nk U κ S
  have hS : 0 ≤ S := by dsimp [S, slackTot]; positivity
  have hSϖ : S ≤ 2 * ϖ * gain * L := by
    have hr := mul_le_mul_of_nonneg_right hρϖ (mul_nonneg hgain.le hL.le)
    dsimp [S, slackTot]
    nlinarith only [hr, hsum']
  have hκ1 : 1 ≤ κ := hpath.1
  have hκ0 : 0 ≤ κ := by linarith
  have hκS : κ ≤ Nk ^ S := hpath.2.1.trans (rpow_mono_exp hNk1 (by
    dsimp [S, slackTot]
    nlinarith only [mul_nonneg (mul_nonneg hρ.le hgain.le) hL.le, hε.le, hτ.le]))
  have hκN : κ ≤ Nk := hpath.2.1.trans (by
    simpa only [Real.rpow_one] using rpow_mono_exp hNk1 (show σ ≤ 1 by linarith))
  have hU0 : 0 ≤ U := by positivity
  have hU1 : 1 ≤ U := Real.one_le_rpow hNk1 (by dsimp [greedySlack]; positivity)
  have hU : U ≤ Nk ^ (4 * S) := rpow_mono_exp hNk1
    (greedySlack_le (mul_nonneg (mul_nonneg hρ.le hgain.le) hL.le) hε.le hσ.le hτ.le)
  have hi : i < m := hsi.2.1
  have hgh : gain ≤ h := hsi.2.2.1
  have hh : 0 < h := hgain.trans_le hgh
  have hroom : r i + 2 * h * L ≤ L := hsi.2.2.2.2.2.1
  have hri : 0 < r i := (hpath.2.2.2.2.1 i hi).2.1
  have hriL : r i + h * L ≤ L := by nlinarith only [hroom, mul_pos hh hL]
  have hscale := sampleInput_sheetScale_bounds hCdisc hdisc hNk1 hL hgain hd₁ hd₁1.le
    hρ.le hδ₀.le hε.le hσ.le hτ.le hδρ hsi hpath hlin
  change 2 ≤ Abound ∧ 4 * U ≤ Abound ∧ 4 * κ ≤ Abound ∧ κ + 1 ≤ Abound ∧ _ at hscale
  have hA : 0 < Abound := by linarith [hscale.1]
  have hA1 : 1 ≤ Abound := by linarith [hscale.1]
  obtain ⟨s₀, hs₀lo, hs₀up⟩ := exists_subBlock_exponent Cs hA1 hκ0
  let K := boxRangeOf κ s₀
  have hKlo : κ * (2 : ℝ) ^ s₀ ≤ K := (boxRangeOf_spec hκ0 s₀).1
  have hKup : (K : ℝ) ≤ κ * (2 : ℝ) ^ s₀ + 1 := (boxRangeOf_spec hκ0 s₀).2
  have hside : side s₀ * (κ + 2) ≤ (Abound ^ (-(Cs : ℝ)) / 128) / 2 :=
    side_le_half_radius hA hκ0 hs₀lo
  have hΛtime : 4 * ((Cs : ℝ) * (25 * (6 : ℝ) + 8) + 1) ≤ Λ := by
    dsimp [Λ, expMult]
    nlinarith only [params.remezExponent_one, (Nat.cast_nonneg Cs : (0 : ℝ) ≤ Cs)]
  have hs₀time := subBlock_time_budget (Kd := Kd) (Cd := 6) (N := Nk) (U := U) (κ := κ) (S := S)
    (κ₁ := κ₁) (θ := θ) (gain := gain) (L := L) (Λ := Λ) (Cs := Cs) (s₀ := s₀)
    hNk1 hS hKd (by norm_num : (0 : ℝ) ≤ 6) hU0 hU hκ0 hκS
    hΛtime hbud.2 (show 0 < κ₁ * θ * gain * L by positivity) hNtime hs₀up
  have hs₀exp : (2 : ℝ) ^ s₀ ≤ Nk ^ tE := hs₀time.trans (by
    rw [← Real.rpow_natCast]
    exact rpow_mono_exp hNk1 (Nat.le_ceil _))
  have hcounts := sample_card_bounds (sE := sE) (Mpr := Mpr) hNk2 hκ0 hκN
    hsi.2.2.2.2.2.2.1 hs₀exp
  have hAformat : Abound ≤ Nk ^ sE :=
    sheetScale_le_pow hNk2 hS hSϖ hKd (by norm_num) hU0 hU hκ0 hκS
  have hlight := error_budget_light (ε := ε) hNk1 hτ hNlight
  obtain ⟨cov, hcovm, hcov, hcovdisj, hcovfloor, hcovmass⟩ :=
    sampleInput_pruned_entries hNk1 hsi hpath hKlo hlight
  have hω : ∀ e, (cov e).Nonempty → 0 < ω (γ (old e.1)) := fun e he => (hcovfloor e he).1
  obtain ⟨H, hH, hHeq, hHsum⟩ := sampleInput_common_caps_sum hNk1 hL hgain hd₁ hd₁1.le
    hρ.le hδ₀.le hε.le hsi hpath hlin hA hs₀up hKup cov hω
  let mG : Group C s₀ K → ℝ := fun G => H G * groupFloor Nk S
  have hfloor (e : Entry n s₀ K) (he : (cov e).Nonempty) :
      ENNReal.ofReal (mG (entryGroup old e)) ≤ ENNReal.ofReal (ω (γ (old e.1))) *
        ((ν (γ (old e.1))).prod volume) (cov e) := by
    dsimp only [mG]
    rw [hHeq e he]
    exact sampleInput_heavy_entry_floor hNk1 hL hgain hd₁ hd₁1.le hρ.le hδ₀.le
      hε.le hσ.le hτ.le hδρ hsi hpath hlin hA hs₀up hKup e.1 (hω e he)
        _ (hcovfloor e he).2
  have hθmass (G : Group C s₀ K) :
      ENNReal.ofReal (groupFloor Nk S) * volume (Metric.closedBall (0 : Real3) (1 / 2)) ≤
        ENNReal.ofReal (mG G / H G) := by
    apply groupFloor_mass_input hNk0
    dsimp only [mG]
    rw [mul_div_cancel_left₀ _ (hH G).ne']
  have hcap (e : Entry n s₀ K) (he : (cov e).Nonempty) :
      (ENNReal.ofReal (ω (γ (old e.1))) • ((ν (γ (old e.1))).prod volume).restrict (cov e)).map
        ((groupBase (T i) (j (old e.1)) (c (old e.1)) (u (old e.1)) (Q (old e.1))
          (subBoxCenter s₀ e.2.1 (boxOf K e.2.2.1)) (Abound ^ (-(Cs : ℝ)) / 128)) ∘
            obs (B (γ (old e.1))) (δ Nk L)) ≤ ENNReal.ofReal (H (entryGroup old e)) • volume := by
    rw [hHeq e he]
    exact sampleInput_weighted_candidate_group_cap hNk1 hsi e.1 c u Q
      ((hpath.2.2.2.2.2.2.2 (old e.1)).2.2).1
      (subBoxCenter s₀ e.2.1 (boxOf K e.2.2.1))
      (by positivity : 0 < Abound ^ (-(Cs : ℝ)) / 128) (fun z hz => (hcov e z hz).1)
  have hcount (G : Group C s₀ K) :
      ((Finset.univ.filter (fun e : Entry n s₀ K => entryGroup old e = G)).card : ℝ) ≤
        cmpRatio Nk (r i) (h * L) ^ (d₁ + εG) := by
    apply sample_hcount (Cs := Cs) (Cd := 6) (Crem := params.remezExponent) hNk1 (by norm_num) (by linarith [params.remezExponent_one]) hρ.le
      hgain hL hε.le hσ.le hτ.le hgh hd₁ hεG hdεG hbud.1 hNcount
    have hc := card_entryGroup_le old G
    have hc' : ((Finset.univ.filter (fun e : Entry n s₀ K => entryGroup old e = G)).card : ℝ) ≤
        2 * ((Finset.univ.filter (fun a => old a = G.1)).card : ℝ) := by exact_mod_cast hc
    exact hc'.trans (mul_le_mul_of_nonneg_left (hsi.2.2.2.2.2.2.2.2.2.1 G.1) (by norm_num))
  obtain ⟨domains, Dcount, hDm, hDsupp, hDcount, hDcard⟩ :=
    sample_domains hNk1 hgain.le hsi hpath cov hcov
  have hlist : ((7 ^ Fintype.card (GroupJetIndex params) * Dcount : ℕ) : ℝ) ≤ Nk ^ β := by
    have hcube := cube_list_budget hNk1 hκ0 hpath.2.1
      (show 0 ≤ 101 * (Clist : ℝ) by positivity) (hσbound.trans hσ₀β) hβ hNlist
    calc
      _ = (Clist : ℝ) * (Dcount : ℝ) := by dsimp only [Clist]; push_cast; ring
      _ ≤ (Clist : ℝ) * (101 * κ ^ 3) := mul_le_mul_of_nonneg_left hDcard (Nat.cast_nonneg _)
      _ = (101 * (Clist : ℝ)) * κ ^ 3 := by ring
      _ ≤ _ := hcube
  have hremezNum := sample_hremez (Cs := Cs) (Cd := 6) (Crem := params.remezExponent)
    (r₀ := r i) hNk1 hS hKd (by norm_num) params.remezScale_one
    params.remezExponent_one hU0 hU hκ0 hκS hεG (by linarith) hgain hL hgh hbud.1 hNremez
  have hwidthNum := sample_hwidth (Cs := Cs) (Cd := 6) (Crem := params.remezExponent)
    (r₀ := r i) hNk1 hS hKd (by norm_num)
    (by linarith [params.remezExponent_one]) hU1 hU hκ0 hκS hεG (by linarith)
    hgain hL hgh hriL hbud.1 hNwidth
  have hthr := sample_hthr (Cs := Cs) (Cd := 6) (Crem := params.remezExponent)
    (r₀ := r i) (fun a : GroupJetIndex params => params.upper a.2.val)
    hNk1 hS hKd (by norm_num) (by linarith [params.remezExponent_one]) hU0 hU hκ0 hκS
    hεG hεG2 hθ.le hθε hgain hL hgh (fun a => (params.upper_pos a.2.val).le)
    params.lower_pos hbud.1 hNthr1 hNthr2
  have hη0 : 0 ≤ U * δ Nk (r i + h * L) * Abound ^ ((Cs : ℝ) + 1) +
      (∑ a, groupJetWidth params (cmpRatio Nk (r i) (h * L)) (δ Nk (r i)) εG a) / params.lower := by
    apply add_nonneg (mul_nonneg (mul_nonneg hU0 (gδ_pos _ _).le) (Real.rpow_nonneg hA.le _))
    exact (sample_jet_budget (fun a : GroupJetIndex params => params.upper a.2.val)
      (fun a => (params.upper_pos a.2.val).le) (one_le_cmpRatio hNk1 (mul_nonneg hh.le hL.le))
      (gδ_pos _ _).le (gδ_le_one hNk1 hri.le) hεG.le params.lower_pos).1
  have hη1 : 340 * (U * δ Nk (r i + h * L) * Abound ^ ((Cs : ℝ) + 1) +
      (∑ a, groupJetWidth params (cmpRatio Nk (r i) (h * L)) (δ Nk (r i)) εG a) / params.lower) ≤ 1 := by
    apply hthr.trans
    have hp : Nk ^ (-(θ * h * L)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNk1
      (by nlinarith only [hθ.le, mul_pos hh hL])
    calc
      _ ≤ 1 * 1 := mul_le_mul (gδ_le_one hNk1 hri.le) hp (by positivity) zero_le_one
      _ = 1 := one_mul _
  have hsource : 8 * Nk ^ Mg ≤ Nk ^ Mc :=
    (sample_budgets (Bw := 1) (Mpr := Mpr) (Mg := Mg) (sE := sE) (tE := tE)
      hNk2 hA1 hAformat (by norm_num) (one_le_pow₀ hNk1)
      (by simpa only [inv_one] using (one_le_pow₀ (n := Mpr) hNk1)) hη0 hη1).1
  have hbudgets (w : Fin W) := sample_budgets (Mg := Mg) (sE := sE) (tE := tE) hNk2 hA1 hAformat
    (hsi.1.2.2.2 w).2.1 (hsi.1.2.2.2 w).2.2.1 (hsi.1.2.2.2 w).2.2.2.1 hη0 hη1
  have hbpair := sample_pair_exponent_le (Cs := Cs) (Cd := 6) (Crem := params.remezExponent) (by norm_num)
    (by linarith [params.remezExponent_one]) hρ.le hgain.le hL.le hε.le hσ.le hτ.le
    hδρ hεG.le hbud.1
  have hpair := error_budget_pair (Cs := Cs) (Cd := 6) (Crem := params.remezExponent) (r₀ := r i) hNk1 (by norm_num)
    (by linarith [params.remezExponent_one]) hρ.le hgain hL hε.le hσ.le hτ.le hgh hεG hεG2
    (by positivity : 0 ≤ (2 : ℝ) ^ (23 : ℕ)) hbpair hbud.1 hNpair
  have hmatch := error_budget_match (Cs := Cs) (Cd := 6) (Crem := params.remezExponent) (r₀ := r i) hNk1 (by norm_num)
    (by linarith [params.remezExponent_one]) hρ.le hgain hL hε.le hσ.le hτ.le hgh hεG hεG2
    hbud.1 hNmatch
  have hmatch' : cmpRatio Nk (r i) (h * L) ^ (-εG) ≤ 1 / 64 := hmatch.trans
    (div_le_div_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hNk1 (by linarith)) (by norm_num))
  have htotal := sample_htotal hcovmass hHsum
    (error_budget_final16 hNk1 hβ (hεbound.trans hε₀β) hNfinal) hmatch' hpair
    (cmpRatio_pos _ _ _) (by positivity) hNk0
  refine ⟨s₀, K, ?_, hcounts.1, hcounts.2.1, ?_⟩
  · rw [pow_add]
    exact mul_le_mul_of_nonneg_left (by convert hs₀time using 1 <;> congr 1 <;> ring) (by positivity)
  · apply coreOutput_of_sample_data hGR
      (group_radius_numeric hNk1 hgain hL hgh (by linarith [params.radius_two]) hNradius)
      (gδ_pos Nk (r i)) hεG hεGp hsheets hNk1 hsi hpath cov hcov hcovm hcovdisj
      hscale.1 hscale.2.1 hscale.2.2.1 hscale.2.2.2.1
      (gδ_le_one hNk1 (by nlinarith only [hri.le, mul_pos hh hL])) (gδ_le_one hNk1 hri.le)
      (fun e _ d => (hscale.2.2.2.2 e.1 d).1)
      (fun G hG d => ?_) hside (groupFloor Nk S) (groupFloor_pos hNk0 S)
      (groupFloor_le_one hNk1 hS) H mG hH hcount hcap hfloor hθmass hremezNum hwidthNum
      hsource
      (fun w => (hbudgets w).2.1) (fun w => (hbudgets w).2.2) hthr
      domains hDm hDsupp Dcount hDcount hcounts.2.2 hlist htotal
    obtain ⟨e, _, heG⟩ := hG
    have hparent : old e.1 = G.1 := congrArg Prod.fst heG
    simpa only [hparent] using (hscale.2.2.2.2 e.1 d).2

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
