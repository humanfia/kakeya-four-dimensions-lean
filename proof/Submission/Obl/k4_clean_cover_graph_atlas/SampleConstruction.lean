import Submission.Obl.k4_clean_cover_graph_atlas.SampleMassData
import Submission.Obl.k4_clean_cover_graph_atlas.SampleComplexity
import Submission.Obl.k4_clean_cover_graph_atlas.ConcreteAssembly
import Submission.Obl.k4_clean_cover_graph_atlas.SampleDiscriminantScale
import Submission.Obl.k4_clean_cover_graph_atlas.SampleTailBounds
import Submission.Obl.k4_clean_cover_graph_atlas.GroupFloorBounds
import Submission.Obl.k4_clean_cover_graph_atlas.EntryGeometryBudget
import Submission.Obl.k4_clean_cover_graph_atlas.Subdivision

/-!
# The per-sample construction from the mass backend

`preparedSampleCore_of_massBackend` proves `PreparedSampleCore` from `SampleMassBackend`: it fixes
all constants and exponents in the quantifier order of `PreparedSampleCore` and, at every late
sample, chooses the common sheet scale `A = sheetScale`, the sub-block exponent `s₀`, the box range
`K = ⌈κ 2^s₀⌉`, the matching ratio `R = δ(r_i)/δ(r_i + hL)`, the spread `M = δ(r_i)`, the matching
exponent `εG`, the Remez fraction `groupFloor`, and the backend's covered incidences and caps, and
calls `coreOutput_of_sample_data`.

Constants (before `ρ`): `Csheet` (stable sheets), `params` (group recovery at `d₀ = d₁`), `Cdisc`
(original discriminant bound), `Kd = discriminantConstant Cdisc`, `Cd = 6`, `εG = matchExp`,
`θ = thetaOf εG`, `Λ = expMult Csheet Cd Crem`, `ϖ = varpiOf εG κ₁ θ Λ`. Before `β`: `Mc` from
`complexity_budget`. After `β`: `N₀` is the maximum of `sampleN0`, the complexity threshold and
the list threshold.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- `expMult` dominates the time-budget multiplier `4 (Cs (25 Cd + 8) + 1)`. -/
theorem expMult_ge_time {Cs : ℕ} {Cd Crem : ℝ} (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem) :
    4 * ((Cs : ℝ) * (25 * Cd + 8) + 1) ≤ expMult Cs Cd Crem := by
  unfold expMult
  nlinarith [mul_nonneg (Nat.cast_nonneg Cs : (0 : ℝ) ≤ Cs) (by linarith : (0 : ℝ) ≤ 25 * Cd + 8)]

/-- **The per-sample construction from the mass backend.** -/
theorem preparedSampleCore_of_massBackend (hmb : SampleMassBackend) : PreparedSampleCore := by
  intro hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  -- fixed constants
  obtain ⟨Csheet, hCs20, hPSF⟩ := exists_packet_sheet_for_lines hsheets
  obtain ⟨params, hGR⟩ := exists_group_recovery hgraph hremez 2 d₁ hd₁ hd₁1
  obtain ⟨Cdisc, hCdisc, hdisc⟩ := exists_packet_discriminant_bound
  set Kd : ℝ := discriminantConstant Cdisc with hKddef
  set Krem : ℝ := params.remezScale with hKremdef
  set Crem : ℝ := params.remezExponent with hCremdef
  set εG : ℝ := matchExp params.epsilon d₁ with hεGdef
  set θ : ℝ := thetaOf εG with hθdef
  set Λ : ℝ := expMult Csheet 6 Crem with hΛdef
  set ϖ : ℝ := varpiOf εG κ₁ θ Λ with hϖdef
  have hKd : 0 ≤ Kd := by rw [hKddef]; unfold discriminantConstant; positivity
  have hKrem : 1 ≤ Krem := params.remezScale_one
  have hCrem : 1 ≤ Crem := params.remezExponent_one
  have hεG : 0 < εG := matchExp_pos params.epsilon_pos hd₁1
  obtain ⟨hεGeps, hdεG, hεG2⟩ := matchExp_le params.epsilon hd₁1.le
  have hθ : 0 < θ := thetaOf_pos hεG
  have hθ4 : θ ≤ 1 / 4 := thetaOf_le_quarter εG
  have hθε : θ ≤ εG / 4 := thetaOf_le εG
  have hΛ : 0 < Λ := expMult_pos (by norm_num) (by linarith)
  have hϖ : 0 < ϖ := varpiOf_pos hεG hκ₁ hθ hΛ
  refine ⟨θ, ϖ, hθ, hθ4, hϖ, ?_⟩
  intro ρ hρ hρϖ hρ4 hdρ L m s gain δ₀ hL hgrid hgain hgain1 hδ₀ hδρ Mp Dp Mg Dg Mpr Dpr
  -- the complexity exponent, fixed before `β`
  set Jconst : ℝ := (∑ k : GroupJetIndex params, params.upper k.2.val) / params.lower with hJdef
  have hJ : 0 ≤ Jconst := by
    rw [hJdef]
    exact div_nonneg (Finset.sum_nonneg fun k _ => (params.upper_pos _).le) params.lower_pos.le
  set tE : ℕ := timeExp κ₁ θ gain L with htEdef
  have hξ : 0 < κ₁ * θ * gain * L := by positivity
  obtain ⟨Mc, N0c, hN0c2, hcomplex⟩ := complexity_budget (scaleExp Kd 6 ϖ gain L : ℝ)
    (8 * ϖ * gain * L) (κ₁ * θ * gain * L / 8) ((tE : ℝ) + 2) Jconst Csheet Mpr Mg
    (Nat.cast_nonneg _) (by positivity) (by positivity) (by positivity) hJ
  refine ⟨Mc, ?_⟩
  intro β ε₀ σ₀ τ hβ hβ1 hε₀ hε₀β hσ₀ hσ₀β hτ hsum
  -- the late-sample threshold
  set Clist : ℝ := 101 * (7 : ℝ) ^ Fintype.card (GroupJetIndex params) with hClistdef
  set N₀ : ℝ := max (sampleN0 Kd 6 Krem Crem Csheet κ₁ θ gain L εG β τ params.radius
      (∑ k : GroupJetIndex params, params.upper k.2.val) params.lower (2 ^ 23) 1)
    (max N0c ((Clist + 1) ^ (1 / (β / 4)))) with hN₀def
  have hN₀2 : 2 ≤ N₀ :=
    (sampleN0_spec (le_max_left _ (max N0c ((Clist + 1) ^ (1 / (β / 4)))))).1
  refine ⟨N₀, hN₀2, ?_⟩
  intro Nk hNk W ω ν E B f hlin ε σ hε hεε₀ hσ hσσ₀ r T nw κ C lev par γ j c u Q R A F lst hpath
    i h n old R' A' V q hsi
  -- thresholds
  have hsN : sampleN0 Kd 6 Krem Crem Csheet κ₁ θ gain L εG β τ params.radius
      (∑ k : GroupJetIndex params, params.upper k.2.val) params.lower (2 ^ 23) 1 ≤ Nk :=
    (le_max_left _ _).trans hNk
  obtain ⟨hN2, hNtime, hNwidth, hNremez, hNthr1, hNthr2, hNcount, hNradius, hNmatch, hNpair,
    hNlight, hNfinal, -⟩ := sampleN0_spec hsN
  have hNc : N0c ≤ Nk := ((le_max_left _ _).trans (le_max_right _ _)).trans hNk
  have hNlist : (Clist + 1) ^ (1 / (β / 4)) ≤ Nk :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hNk
  have hN1 : 1 ≤ Nk := by linarith
  have hNpos : 0 < Nk := by linarith
  -- the path and the sample input
  have hκ1 : 1 ≤ κ := hpath.1
  have hκ0 : 0 ≤ κ := by linarith
  have hκN : κ ≤ Nk ^ σ := hpath.2.1
  obtain ⟨hscalar, hi, hgh, hh18, -, hmargin, hn, hentry, -, hcountOld, -⟩ := id hsi
  have hh : 0 < h := lt_of_lt_of_le hgain hgh
  have hε0 : 0 ≤ ε := hε.le
  have hσ0 : 0 ≤ σ := hσ.le
  have hτ0 : 0 ≤ τ := hτ.le
  have hσ1 : σ ≤ 1 := by linarith
  -- slack budgets
  have hsum' : ε + σ + τ ≤ ϖ * gain * L := by linarith
  obtain ⟨hbudε, hbudκ⟩ := slack_budget (εG := εG) (κ₁ := κ₁) (θ := θ) hΛ hρϖ hgain hL hsum'
  set S : ℝ := slackTot ρ gain L ε σ τ with hSdef
  have hgL : 0 < gain * L := mul_pos hgain hL
  have hρgL : ρ * gain * L ≤ ϖ * gain * L := by
    have := mul_le_mul_of_nonneg_right hρϖ hgL.le
    calc ρ * gain * L = ρ * (gain * L) := by ring
      _ ≤ ϖ * (gain * L) := this
      _ = ϖ * gain * L := by ring
  have hρgL0 : 0 ≤ ρ * gain * L := by positivity
  have hS0 : 0 ≤ S := by rw [hSdef]; unfold slackTot; positivity
  have hSϖ : S ≤ 2 * ϖ * gain * L := by rw [hSdef]; unfold slackTot; linarith
  have hσS : σ ≤ S := by rw [hSdef]; unfold slackTot; linarith
  set U : ℝ := Nk ^ greedySlack ρ gain L ε with hUdef
  have hgS : greedySlack ρ gain L ε ≤ 4 * S := greedySlack_le hρgL0 hε0 hσ0 hτ0
  have hgs0 : 0 ≤ greedySlack ρ gain L ε := by unfold greedySlack; positivity
  have hU0 : 0 ≤ U := by positivity
  have hU1 : 1 ≤ U := Real.one_le_rpow hN1 hgs0
  have hU4S : U ≤ Nk ^ (4 * S) := rpow_mono_exp hN1 hgS
  have hκS : κ ≤ Nk ^ S := hκN.trans (rpow_mono_exp hN1 hσS)
  -- the common sheet scale and the discriminant certificates
  have hsc := sampleInput_sheetScale_bounds hCdisc hdisc hN1 hL hgain hd₁ hd₁1.le hρ.le hδ₀.le
    hε0 hσ0 hτ0 hδρ hsi hpath hlin
  set Aval : ℝ := sheetScale Kd 6 Nk U κ S with hAdef
  obtain ⟨hA2, hUA, hκ4A, hκA, hcoefs⟩ := hsc
  obtain ⟨hδf1, hδo1⟩ := sampleInput_thickness_bounds hN1 hL.le hgain.le hsi hpath
  have hApos : 0 < Aval := by linarith
  have hA1 : 1 ≤ Aval := by linarith
  -- the sub-block exponent and the box range
  obtain ⟨s₀, hs₀lo, hs₀hi⟩ := exists_subBlock_exponent Csheet hA1 hκ0
  set K : ℕ := ⌈κ * (2 : ℝ) ^ s₀⌉₊ with hKdef
  have hKlo : κ * (2 : ℝ) ^ s₀ ≤ K := Nat.le_ceil _
  have hKhi : (K : ℝ) ≤ κ * (2 : ℝ) ^ s₀ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hside : side s₀ * (κ + 2) ≤ (Aval ^ (-(Csheet : ℝ)) / 128) / 2 :=
    side_le_half_radius hApos hκ0 hs₀lo
  have htime : (2 : ℝ) ^ s₀ ≤ Nk ^ (κ₁ * θ * gain * L / 8) :=
    subBlock_time_budget hN1 hS0 hKd (by norm_num) hU0 hU4S hκ0 hκS
      (expMult_ge_time (by norm_num) (by linarith)) hbudκ hξ hNtime hs₀hi
  -- the mass backend
  have hlight : 4 * Nk ^ (-ε - τ) ≤ Nk ^ (-ε) / 64 := error_budget_light hN1 hτ hNlight
  have hs512 : (2 : ℝ) ^ s₀ ≤ 512 * (κ + 2) * Aval ^ (Csheet : ℝ) :=
    hs₀hi.trans_eq (by ring)
  obtain ⟨cov, H, hcovm, hcov, hcovdisj, hHpos, hcap, hfloor, htot, hHsum⟩ :=
    hmb hN1 hL hgain hd₁ hd₁1.le hρ.le hδ₀.le hε0 hσ0 hτ hδρ hsi hpath hlin Aval Csheet s₀ K
      hApos hs512 hKlo hKhi hlight
  -- the observation domains
  obtain ⟨Sdom, Dcount, hSm, hsupp, hD, hDκ⟩ := sample_domains hN1 hgain.le hsi hpath cov hcov
  -- the matching ratio
  set Rg : ℝ := cmpRatio Nk (r i) (h * L) with hRgdef
  have hhL : 0 ≤ h * L := (mul_pos hh hL).le
  have hRg1 : 1 ≤ Rg := one_le_cmpRatio hN1 hhL
  have hRgpos : 0 < Rg := by linarith
  -- sizes
  have htwo : (2 : ℝ) ^ s₀ ≤ Nk ^ tE := by
    refine htime.trans ?_
    rw [← Real.rpow_natCast]
    exact rpow_mono_exp hN1 (Nat.le_ceil _)
  have hκN1 : κ ≤ Nk ^ (1 : ℕ) := by
    rw [pow_one]
    exact hκN.trans ((rpow_mono_exp hN1 hσ1).trans_eq (Real.rpow_one Nk))
  have hKN : (K : ℝ) ≤ Nk ^ (1 + tE + 1) := ceil_box_range_bound hN2 hκ0 hκN1 htwo
  have hKNr : (K : ℝ) ≤ Nk ^ ((tE : ℝ) + 2) := by
    rw [show (tE : ℝ) + 2 = ((1 + tE + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact hKN
  obtain ⟨hcplx1, hcplx2, hcplx3⟩ := hcomplex Nk hNc
  have hAN : Aval ≤ Nk ^ (scaleExp Kd 6 ϖ gain L : ℝ) := by
    rw [Real.rpow_natCast]
    exact sheetScale_le_pow hN2 hS0 hSϖ hKd (by norm_num) hU0 hU4S hκ0 hκS
  have hUN : U ≤ Nk ^ (8 * ϖ * gain * L) := rpow_mono_exp hN1 (by linarith)
  obtain ⟨hcardE, h2s₀, hKMc⟩ := hcplx3 n s₀ K hn htime hKNr
  -- the jet budget
  have hjet := sample_jet_budget (fun k : GroupJetIndex params => params.upper k.2.val)
    (fun k => (params.upper_pos _).le) hRg1 (gδ_pos Nk (r i)).le hδo1 hεG.le params.lower_pos
  refine ⟨s₀, K, ?_, h2s₀, hKMc, ?_⟩
  · rw [pow_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact htime.trans_eq (by congr 1; ring)
  · -- the hypotheses of the concrete assembly
    have hB : ∀ w, 0 < B w := fun w => (hscalar.2.2.2 w).2.1
    have hBM : ∀ w, B w ≤ Nk ^ Mpr := fun w => (hscalar.2.2.2 w).2.2.1
    have hBi : ∀ w, (B w)⁻¹ ≤ Nk ^ Mpr := fun w => (hscalar.2.2.2 w).2.2.2.1
    have hhcount : ∀ G : Group C s₀ K,
        ((Finset.univ.filter (fun e : Entry n s₀ K => entryGroup old e = G)).card : ℝ) ≤
          Rg ^ (d₁ + εG) := by
      intro G
      have h1 := card_entryGroup_le old G
      have h2 := hcountOld G.1
      refine sample_hcount (Cs := Csheet) (Cd := 6) (Crem := Crem) (σ := σ) (τ := τ) hN1
        (by norm_num) (by linarith) hρ.le hgain hL hε0 hσ0 hτ0 hgh hd₁ hεG hdεG hbudε hNcount ?_
      calc ((Finset.univ.filter (fun e : Entry n s₀ K => entryGroup old e = G)).card : ℝ)
          ≤ ((2 * (Finset.univ.filter (fun a => old a = G.1)).card : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ = 2 * ((Finset.univ.filter (fun a => old a = G.1)).card : ℝ) := by push_cast; ring
        _ ≤ 2 * Nk ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε) := by linarith
    have hθmass : ∀ G : Group C s₀ K,
        ENNReal.ofReal (groupFloor Nk S) * volume (Metric.closedBall (0 : Real3) (1 / 2)) ≤
          ENNReal.ofReal (H G * groupFloor Nk S / H G) := by
      intro G
      refine groupFloor_mass_input hNpos (le_of_eq ?_)
      field_simp [(hHpos G).ne']
    have hremez' := sample_hremez (Cs := Csheet) (r₀ := r i) (h := h) hN1 hS0 hKd
      (by norm_num) hKrem hCrem hU0 hU4S hκ0 hκS hεG (by linarith) hgain hL hgh hbudε hNremez
    have hwidth' := sample_hwidth (Cs := Csheet) (r₀ := r i) hN1 hS0 hKd (by norm_num)
      (by linarith) hU1 hU4S hκ0 hκS hεG (by linarith) hgain hL hgh (by linarith) hbudε hNwidth
    have hthr' := sample_hthr (fun k : GroupJetIndex params => params.upper k.2.val)
      (Cs := Csheet) (r₀ := r i) hN1 hS0 hKd (by norm_num) (by linarith) hU0 hU4S hκ0 hκS hεG
      hεG2 hθ.le hθε hgain hL hgh (fun k => (params.upper_pos _).le) params.lower_pos hbudε
      hNthr1 hNthr2
    have hR : params.radius ≤ Rg :=
      group_radius_numeric hN1 hgain hL hgh (by linarith [params.radius_two]) hNradius
    have hlistβ : ((7 ^ Fintype.card (GroupJetIndex params) * Dcount : ℕ) : ℝ) ≤ Nk ^ β := by
      have hC0 : 0 ≤ Clist := by rw [hClistdef]; positivity
      have hcube := cube_list_budget hN1 hκ0 hκN hC0 (by linarith : σ ≤ β / 4) hβ hNlist
      push_cast
      calc (7 : ℝ) ^ Fintype.card (GroupJetIndex params) * (Dcount : ℝ)
          ≤ 7 ^ Fintype.card (GroupJetIndex params) * (101 * κ ^ 3) := by gcongr
        _ = Clist * κ ^ 3 := by rw [hClistdef]; ring
        _ ≤ Nk ^ β := hcube
    have hmatch : Rg ^ (-εG) ≤ 1 / 64 := by
      have h1 := error_budget_match (Cs := Csheet) (Cd := 6) (Crem := Crem) (r₀ := r i) hN1
        (by norm_num) (by linarith) hρ.le hgain hL hε0 hσ0 hτ0 hgh hεG hεG2 hbudε hNmatch
      have h2 : Nk ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      linarith
    have hpair : 2 ^ 23 * Nk ^ capLoss ρ gain L δ₀ ε τ σ * Rg ^ (-(2 * εG)) ≤ Nk ^ (-ε) / 64 :=
      error_budget_pair (Cs := Csheet) (Cd := 6) (Crem := Crem) (r₀ := r i) hN1 (by norm_num)
        (by linarith) hρ.le hgain hL hε0 hσ0 hτ0 hgh hεG hεG2 (by positivity)
        (sample_pair_exponent_le (Cs := Csheet) (by norm_num) (by linarith) hρ.le hgain.le hL.le
          hε0 hσ0 hτ0 hδρ hεG.le hbudε) hbudε hNpair
    have hhtotal := sample_htotal (N := Nk) (β := β) (ε := ε) (Rg := Rg) (εg := εG)
      (K₀ := 2 ^ 23) (b := capLoss ρ gain L δ₀ ε τ σ) htot hHsum
      (error_budget_final16 hN1 hβ (by linarith) hNfinal) hmatch hpair hRgpos (by positivity)
      hNpos
    have hJb0 := hjet.1
    have hJbc := hjet.2
    have hbudgets := fun w => hcplx1 Aval U (δ Nk (r i + h * L)) (B w)
      ((∑ k : GroupJetIndex params, params.upper k.2.val * (δ Nk (r i) * Rg ^ (-εG))) /
        params.lower) hA2 hAN hU0 hUN (gδ_pos Nk _) hδf1 (hB w) (hBM w) (hBi w) hJb0 hJbc
    exact coreOutput_of_sample_data hGR hR (gδ_pos Nk (r i)) hεG hεGeps hPSF hN1 hsi hpath cov
      hcov hcovm hcovdisj hA2 hUA hκ4A hκA hδf1 hδo1 (fun e _ d => (hcoefs e.1 d).1)
      (by rintro G ⟨e, -, rfl⟩ d; exact (hcoefs e.1 d).2) hside (groupFloor Nk S)
      (groupFloor_pos hNpos S) (groupFloor_le_one hN1 hS0) H (fun G => H G * groupFloor Nk S)
      hHpos hhcount hcap hfloor hθmass hremez' hwidth' hcplx2 (fun w => (hbudgets w).2)
      (fun w => (hbudgets w).1) hthr' Sdom hSm hsupp Dcount hD hcardE hlistβ hhtotal

end Submission.Obl.k4_clean_cover_graph_atlas
