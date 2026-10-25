-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Final.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.FinalAux
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ZoomBridge

/-!
# Local grid linearity from the slab lemma and criticality (sticky Lemma 5.4)

For every output error `ε` and scale margin `κ`, a family regular at a sufficiently small error
is refined to non-horizontal shadings, decomposed at the coarse scale `≈ ρ δ ^ ε₁ / 4` by the
two-scale theorem (which uses that there are no examples above `σ`), and the slab lemma is
applied in the heavy windows of all cells of height `√ρ`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal

/-- The small-`δ` conditions of the final bookkeeping. -/
lemma small_conditions {κ' ε₁ εl εv ηl ρ₀ ε : ℝ} (h1 : 0 < κ' - 2 * ε₁) (h2 : 0 < κ' - ε₁)
    (h3 : 0 < κ') (h4 : 0 < ρ₀) (h5 : 0 < κ' * (1 / 2 - εl)) (h6 : 0 < κ' * ηl - εv)
    (h7 : 0 < 1 - εv) (h8 : 0 < κ' - εv) (h9 : 0 < κ' * (ηl - ε₁) - 6 * εv - 3 * ε₁)
    (h10 : 0 < κ' / 2 - 2 * εv - ε₁) (h11 : 0 < ε - εl - 3 / 2 * ε₁) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      4 * δ ^ (κ' - 2 * ε₁) ≤ 1 ∧ 64 * δ ^ (κ' - ε₁) ≤ 1 ∧ 10 ^ 6 / 4 * δ ^ κ' ≤ 1 ∧
      1 / (4 * ρ₀) * δ ^ κ' ≤ 1 ∧ 8 * δ ^ (κ' * (1 / 2 - εl)) ≤ 1 ∧
      162 * δ ^ (κ' * ηl - εv) ≤ 1 ∧ 6 * δ ^ (κ' * ηl - εv) ≤ 1 ∧ 6 * δ ^ (1 - εv) ≤ 1 ∧
      48 * δ ^ (κ' - εv) ≤ 1 ∧
      3600 / 9 * (16 * 2304 * 2048 * 1280) * δ ^ (κ' * (ηl - ε₁) - 6 * εv - 3 * ε₁) ≤ 1 ∧
      1920 * δ ^ (κ' / 2 - 2 * εv - ε₁) ≤ 1 ∧
      73728 * 64 ^ εl * δ ^ (ε - εl - 3 / 2 * ε₁) ≤ 1 := by
  exact Reg.small_and (Reg.cut_le_one h1 4) <| Reg.small_and (Reg.cut_le_one h2 64) <|
    Reg.small_and (Reg.cut_le_one h3 _) <| Reg.small_and (Reg.cut_le_one h3 _) <|
    Reg.small_and (Reg.cut_le_one h5 8) <| Reg.small_and (Reg.cut_le_one h6 162) <|
    Reg.small_and (Reg.cut_le_one h6 6) <| Reg.small_and (Reg.cut_le_one h7 6) <|
    Reg.small_and (Reg.cut_le_one h8 48) <| Reg.small_and (Reg.cut_le_one h9 _) <|
    Reg.small_and (Reg.cut_le_one h10 1920) (Reg.cut_le_one h11 _)

/-- `δ ^ a ≤ c` from `C δ ^ a ≤ 1`. -/
lemma rpow_le_of_mul {δ a C : ℝ} (hC : 0 < C) (h : C * δ ^ a ≤ 1) : δ ^ a ≤ 1 / C := by
  rw [le_div_iff₀ hC, mul_comm]; exact h

set_option maxHeartbeats 4000000 in
/-- Sticky Lemma 5.4 in the form of local grid linearity. -/
theorem localGridLinearity_of_slab {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hlin : SlabLinearity) (hcrit : ∀ t, σ < t → ¬ Coarse.Examples t) :
    Reg.LocalGridLinearity σ := by
  intro ε κ hε hκ
  -- parameters
  set κ' := min κ (1 / 4) with hκ'
  have hκ'0 : 0 < κ' := lt_min hκ (by norm_num)
  have hκ'κ : κ' ≤ κ := min_le_left _ _
  have hκ'4 : κ' ≤ 1 / 4 := min_le_right _ _
  set εl := min (ε / 8) (1 / 8) with hεl
  have hεl0 : 0 < εl := lt_min (by positivity) (by norm_num)
  have hεl8 : εl ≤ ε / 8 := min_le_left _ _
  have hεl1 : εl ≤ 1 / 8 := min_le_right _ _
  obtain ⟨ηl, ρ₀, hηl, hρ₀, hspec⟩ := hlin σ hσ0 hσ1 εl hεl0
  set m := min ηl 1 with hm
  have hm0 : 0 < m := lt_min hηl one_pos
  have hmη : m ≤ ηl := min_le_left _ _
  have hm1 : m ≤ 1 := min_le_right _ _
  set μ := κ' * m / 100 with hμ
  have hμ0 : 0 < μ := by positivity
  have hμη : μ ≤ κ' * ηl / 100 := by
    have := mul_le_mul_of_nonneg_left hmη hκ'0.le
    rw [hμ]; linarith
  have hμ1 : μ ≤ κ' / 100 := by
    have := mul_le_mul_of_nonneg_left hm1 hκ'0.le
    rw [hμ]; linarith
  set ε₁ := min (ε / 8) μ with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) hμ0
  have hε₁8 : ε₁ ≤ ε / 8 := min_le_left _ _
  have hε₁μ : ε₁ ≤ μ := min_le_right _ _
  have hκηl4 : κ' * ηl ≤ ηl / 4 := by nlinarith
  have hε₁η : ε₁ < ηl := by linarith
  obtain ⟨ηts, dts, hηts, hdts, hTS⟩ := Coarse.two_scale_theorem hcrit ε₁ hε₁0
  set εv := min μ ηts with hεv
  have hεv0 : 0 < εv := lt_min hμ0 hηts
  have hεvμ : εv ≤ μ := min_le_left _ _
  have hεvts : εv ≤ ηts := min_le_right _ _
  obtain ⟨ηv, dv, hηv, -, hdv, hvert⟩ := Reg.vertical_refinement hσ0 hσ1 hεv0
  have hκηl : 0 < κ' * ηl := mul_pos hκ'0 hηl
  obtain ⟨d₁, hd₁, hsmall⟩ := small_conditions (κ' := κ') (ε₁ := ε₁) (εl := εl) (εv := εv)
    (ηl := ηl) (ρ₀ := ρ₀) (ε := ε) (by linarith) (by linarith) hκ'0 hρ₀
    (by nlinarith) (by linarith) (by linarith) (by linarith)
    (by nlinarith) (by linarith) (by linarith)
  refine ⟨min ηv ε, min (min dv dts) d₁, lt_min hηv hε, min_le_right _ _,
    lt_min (lt_min hdv hdts) hd₁, ?_⟩
  intro δ hδ hδd ρ hρ1 hρ2 G Y hY
  have hδdv : δ ≤ dv := hδd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδdts : δ ≤ dts := hδd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδd₁ : δ ≤ d₁ := hδd.trans (min_le_right _ _)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := hsmall δ hδ hδd₁
  obtain ⟨hδ100, hYext, hYgr, hf, hfb⟩ := hY
  have hδ1 : δ ≤ 1 := by linarith
  -- the scale `ρ` with the margin `κ'`
  have hρκ1 : δ ^ (1 - κ') ≤ ρ :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans hρ1
  have hρκ2 : ρ ≤ δ ^ κ' := hρ2.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hκ'κ)
  have hρpos : 0 < ρ := (Real.rpow_pos_of_pos hδ _).trans_le hρκ1
  have hρ1' : ρ ≤ 1 := hρκ2.trans (Real.rpow_le_one hδ.le hδ1 hκ'0.le)
  -- vertical refinement
  have hYext' : Reg.ExtremalFamily σ ηv δ G.n G.x G.v Y :=
    hYext.mono_error hδ hδ1 (min_le_left _ _)
  have hYgr' : Reg.Grains σ δ (δ ^ (-ηv)) G.v Y G.f G.P :=
    hYgr.mono_constant hδ (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by
      have := min_le_left ηv ε; linarith))
  obtain ⟨Z, hZY, hZext, hZgr, hZvert⟩ :=
    hvert δ hδ hδdv hδ100 G.n G.x G.v Y G.f G.P hYext' hf hYgr'
  -- the two-scale decomposition at `r = ρ δ ^ ε₁ / 4`
  set r := ρ * δ ^ ε₁ / 4 with hr
  have hδε₁ : 0 < δ ^ ε₁ := Real.rpow_pos_of_pos hδ _
  have hr1 : δ ^ (1 - ε₁) ≤ r := by
    have e : δ ^ (1 - ε₁) = δ ^ (1 - κ') * δ ^ ε₁ * δ ^ (κ' - 2 * ε₁) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
    have hc : δ ^ (κ' - 2 * ε₁) ≤ 1 / 4 := rpow_le_of_mul (by norm_num) c1
    rw [e, hr]
    have := mul_le_mul_of_nonneg_right hρκ1 hδε₁.le
    have hpos : 0 ≤ δ ^ (1 - κ') * δ ^ ε₁ := by positivity
    calc δ ^ (1 - κ') * δ ^ ε₁ * δ ^ (κ' - 2 * ε₁) ≤ δ ^ (1 - κ') * δ ^ ε₁ * (1 / 4) :=
          mul_le_mul_of_nonneg_left hc hpos
      _ ≤ ρ * δ ^ ε₁ / 4 := by linarith
  have hr2 : r ≤ δ ^ ε₁ := by
    rw [hr]
    have := mul_le_mul_of_nonneg_right hρ1' hδε₁.le
    linarith
  have hZfam : Coarse.Family ηts δ G.n G.x G.v Z :=
    Coarse.Family.mono_error (η := εv) hZext.1 hδ hδ1 hεvts
  have hZsep : Coarse.Separated ηts δ G.n G.x G.v :=
    Coarse.Separated.mono_error (η := εv) (Reg.flat_of_strong hZext.2.1) hδ hδ1 hεvts
  have hZvol : volume (⋃ i, Z i) ≤ ENNReal.ofReal (δ ^ (σ - ηts)) :=
    hZext.2.2.2.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))
  obtain ⟨ρc, hrρc, hρcr, Y', k, z, w, Yt, a, s, Mc, hY'Z, hY'm, hY'mass, hYtfam, -, -, hcov, -,
      hs0, hgrid, -, -, hcm, -, -, -, hs16, hsρc, hbal, -⟩ :=
    hTS δ hδ hδdts hδ100 G.n G.x G.v Z hZfam hZsep hZvol r hr1 hr2
  have hk : 0 < k := hYtfam.1
  have hn : 0 < G.n := hYext.1.1
  have hnr : (0 : ℝ) < G.n := by exact_mod_cast hn
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  -- bounds for the grid side `s`
  have hρc_le : ρc ≤ ρ / 4 := by
    refine hρcr.trans (le_of_eq ?_)
    rw [hr, Real.rpow_neg hδ.le]; field_simp
  have hs_le : s ≤ ρ / 4 := hsρc.trans hρc_le
  have hs_ge : ρ * δ ^ ε₁ / 64 ≤ s := by
    have : r / 16 ≤ s := by linarith
    rw [hr] at this; linarith
  have hκε : δ ^ (1 - κ' + ε₁) ≤ ρ * δ ^ ε₁ := by
    have e : δ ^ (1 - κ' + ε₁) = δ ^ (1 - κ') * δ ^ ε₁ := Real.rpow_add hδ _ _
    rw [e]; exact mul_le_mul_of_nonneg_right hρκ1 hδε₁.le
  have hs_ge2 : δ / 64 ≤ s := by
    have : δ ≤ δ ^ (1 - κ' + ε₁) := by
      calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
        _ ≤ δ ^ (1 - κ' + ε₁) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    linarith
  have hδs : δ ≤ s := by
    have hc : δ ^ (κ' - ε₁) ≤ 1 / 64 := rpow_le_of_mul (by norm_num) c2
    have e : δ = δ ^ (1 - κ' + ε₁) * δ ^ (κ' - ε₁) := by
      rw [← Real.rpow_add hδ]; simp
    have hpos : 0 ≤ δ ^ (1 - κ' + ε₁) := Real.rpow_nonneg hδ.le _
    calc δ = δ ^ (1 - κ' + ε₁) * δ ^ (κ' - ε₁) := e
      _ ≤ δ ^ (1 - κ' + ε₁) * (1 / 64) := mul_le_mul_of_nonneg_left hc hpos
      _ ≤ s := by linarith
  have hδκ : δ ^ κ' ≤ 4 / 10 ^ 6 := by
    have := rpow_le_of_mul (by norm_num) c3; norm_num at this ⊢; linarith
  have hs_small : s ≤ 1 / 10 ^ 6 := by linarith
  have hsρ₀ : s ≤ ρ₀ := by
    have := rpow_le_of_mul (by positivity) c4
    rw [one_div_one_div] at this
    linarith
  have hs_pos : 0 < s := hs0
  have hsκ : s ≤ δ ^ κ' := by linarith
  -- the fine setup
  set θv := δ ^ εv with hθv
  set Kv := δ ^ (-εv) with hKv
  set Nc := 8 * (ρc ^ (2 - σ - ε₁) * k) * (δ ^ (-ε₁) * ((G.n : ℝ) / k)) with hNc
  have hθv0 : 0 < θv := Real.rpow_pos_of_pos hδ _
  have hθv1 : θv ≤ 1 := Real.rpow_le_one hδ.le hδ1 hεv0.le
  have hKv1 : 1 ≤ Kv := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hρcpos : 0 < ρc := lt_of_lt_of_le (by positivity) hrρc
  have hc4 : 0 < 1 - 4 * ρc := by linarith
  have hZball : (⋃ i, Z i) ⊆ ball (0 : Space) 1 :=
    iUnion_subset fun i => (hZext.1.2.2.2.2.2.1 i).trans (hZext.1.2.2.1 i)
  have hS : FineSetup σ δ s θv Kv Nc G.x G.v Y' (⋃ i, Z i) G.f G.P :=
    { σ_pos := hσ0, σ_lt := hσ1, δ_pos := hδ, δ_le := hδs, s_small := hs_small,
      θ_pos := hθv0, θ_le := hθv1, K_one := hKv1, f_lip := hf, f_bound := hfb,
      P_lip := hZgr.2.1, Eo_ball := hZball, glob := hZgr.1, loc := hZgr.2.2.2.2,
      unit := hZgr.2.2.1, meas := hY'm,
      sub_Eo := fun i => (hY'Z i).trans (subset_iUnion Z i),
      sub_tube := fun i => (hY'Z i).trans (hZext.1.2.2.2.2.2.1 i),
      v_unit := hZext.1.2.1,
      perp := fun i p hp => hZgr.2.2.2.1 i p (hY'Z i hp),
      vert := fun i hne => hZvert i ((hne.mono (hY'Z i)).ne_empty),
      cube := fun m => card_meeting_cube_le hs0 hc4 (by linarith)
        (by positivity) (by positivity) hcov hgrid hcm hbal m }
  have hYb : ∀ i, Y' i ⊆ ball (0 : Space) 1 := fun i => (hS.sub_Eo i).trans hS.Eo_ball
  -- the total refined mass
  set M := (heightMass Y' (Icc (-1) 1)).toReal with hM
  have hMlow : δ ^ ε₁ * G.n * δ ^ 2 ≤ M := by
    rw [hM, heightMass_total hYb]
    have hfin : ∑ i, volume (Y' i) ≠ ∞ := by
      apply ne_of_lt; apply ENNReal.sum_lt_top.mpr; intro i _
      exact (measure_mono (hYb i)).trans_lt measure_ball_lt_top
    have := ENNReal.toReal_mono hfin hY'mass
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  -- the numerical hypotheses of the cells
  have hs8 : 8 * s ≤ s ^ ((1 : ℝ) / 2 + εl) := by
    have h1 : s ^ ((1 : ℝ) / 2 - εl) ≤ δ ^ (κ' * (1 / 2 - εl)) := by
      rw [Real.rpow_mul hδ.le]
      exact Real.rpow_le_rpow hs_pos.le hsκ (by linarith)
    have h2 : 8 * s ^ ((1 : ℝ) / 2 - εl) ≤ 1 := by linarith
    have e : s = s ^ ((1 : ℝ) / 2 + εl) * s ^ ((1 : ℝ) / 2 - εl) := by
      rw [← Real.rpow_add hs_pos]; norm_num
    have hp : 0 ≤ s ^ ((1 : ℝ) / 2 + εl) := Real.rpow_nonneg hs_pos.le _
    calc 8 * s = s ^ ((1 : ℝ) / 2 + εl) * (8 * s ^ ((1 : ℝ) / 2 - εl)) := by
          conv_lhs => rw [e]
          ring
      _ ≤ s ^ ((1 : ℝ) / 2 + εl) * 1 := mul_le_mul_of_nonneg_left h2 hp
      _ = _ := mul_one _
  have hK : 162 * Kv ≤ s ^ (-ηl) := by
    have h1 : δ ^ (-(κ' * ηl)) ≤ s ^ (-ηl) := by
      rw [show -(κ' * ηl) = κ' * (-ηl) by ring, Real.rpow_mul hδ.le]
      exact Real.rpow_le_rpow_of_nonpos hs_pos hsκ (by linarith)
    have e : Kv = δ ^ (κ' * ηl - εv) * δ ^ (-(κ' * ηl)) := by
      rw [hKv, ← Real.rpow_add hδ]; congr 1; ring
    rw [e]
    have hp : 0 ≤ δ ^ (-(κ' * ηl)) := Real.rpow_nonneg hδ.le _
    calc 162 * (δ ^ (κ' * ηl - εv) * δ ^ (-(κ' * ηl))) = (162 * δ ^ (κ' * ηl - εv)) *
          δ ^ (-(κ' * ηl)) := by ring
      _ ≤ 1 * δ ^ (-(κ' * ηl)) := mul_le_mul_of_nonneg_right c6 hp
      _ ≤ s ^ (-ηl) := by rw [one_mul]; exact h1
  have hθη : s ^ ηl ≤ (θv - δ) / 2 - 8 * s := by
    have h1 : s ^ ηl ≤ δ ^ (κ' * ηl) := by
      rw [Real.rpow_mul hδ.le]; exact Real.rpow_le_rpow hs_pos.le hsκ hηl.le
    have a1 : δ ^ (κ' * ηl) ≤ θv / 6 := by
      have e : δ ^ (κ' * ηl - εv) * δ ^ εv = δ ^ (κ' * ηl) := by
        rw [← Real.rpow_add hδ, show κ' * ηl - εv + εv = κ' * ηl by ring]
      have := mul_le_mul_of_nonneg_right (rpow_le_of_mul (by norm_num) c7) hθv0.le
      rw [← e]; linarith
    have a2 : δ ≤ θv / 6 := by
      have e : δ ^ (1 - εv) * δ ^ εv = δ := by
        rw [← Real.rpow_add hδ, show 1 - εv + εv = (1 : ℝ) by ring, Real.rpow_one]
      have := mul_le_mul_of_nonneg_right (rpow_le_of_mul (by norm_num) c8) hθv0.le
      rw [← e]; linarith
    have a3 : δ ^ κ' ≤ θv / 48 := by
      have e : δ ^ (κ' - εv) * δ ^ εv = δ ^ κ' := by
        rw [← Real.rpow_add hδ, show κ' - εv + εv = κ' by ring]
      have := mul_le_mul_of_nonneg_right (rpow_le_of_mul (by norm_num) c9) hθv0.le
      rw [← e]; linarith
    linarith
  -- the heavy windows
  have hL := winLen_spec hs_pos (by linarith)
  have hLle : (winLen s : ℝ) ≤ 1 / Real.sqrt s := by
    have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs_pos
    rw [le_div_iff₀ hsp]
    have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs_pos.le
    nlinarith [hL.2.1]
  have hkey : 3600 / 9 * (16 * 2304 * 2048 * 1280) * Kv * θv⁻¹ ^ 5 * δ ^ (-(3 * ε₁)) *
      s ^ (ηl - ε₁) ≤ 1 := by
    have h1 : s ^ (ηl - ε₁) ≤ δ ^ (κ' * (ηl - ε₁)) := by
      rw [Real.rpow_mul hδ.le]; exact Real.rpow_le_rpow hs_pos.le hsκ (by linarith)
    have e : Kv * θv⁻¹ ^ 5 * δ ^ (-(3 * ε₁)) * δ ^ (κ' * (ηl - ε₁)) =
        δ ^ (κ' * (ηl - ε₁) - 6 * εv - 3 * ε₁) := by
      rw [hKv, hθv, ← Real.rpow_neg hδ.le, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le,
        ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 1; push_cast; ring
    have hp : 0 ≤ 3600 / 9 * (16 * 2304 * 2048 * 1280) * Kv * θv⁻¹ ^ 5 * δ ^ (-(3 * ε₁)) := by
      positivity
    calc 3600 / 9 * (16 * 2304 * 2048 * 1280) * Kv * θv⁻¹ ^ 5 * δ ^ (-(3 * ε₁)) * s ^ (ηl - ε₁)
        ≤ 3600 / 9 * (16 * 2304 * 2048 * 1280) * Kv * θv⁻¹ ^ 5 * δ ^ (-(3 * ε₁)) *
          δ ^ (κ' * (ηl - ε₁)) := mul_le_mul_of_nonneg_left h1 hp
      _ = 3600 / 9 * (16 * 2304 * 2048 * 1280) * δ ^ (κ' * (ηl - ε₁) - 6 * εv - 3 * ε₁) := by
          rw [← e]; ring
      _ ≤ 1 := c10
  have hheavy : ∀ Mw : ℝ, Real.sqrt s * M / 60 ≤ Mw →
      s ^ (1 + σ / 2 + ηl) ≤ 9 * s * θv ^ 4 * Mw ^ 2 / (16 * 2304 * Nc * δ ^ 4 *
        pieceBound σ δ s θv Kv ((winLen s : ℝ) * s) * winLen s * G.n) := by
    intro Mw hMw
    have hb := sqrt_s_bounds hS
    exact hvol_of_heavy hσ0 hσ1 hδ hδs hθv0 (by linarith) hε₁0 hnr (by positivity)
      (cube_count_le hσ0 hσ1 hε₁0 (by linarith) hδ hρcpos (by linarith) hkr hnr.le)
      (pieceBound_pos hs_pos (by linarith) hθv0 hδ.le (by positivity))
      (pieceBound_le hσ0 hσ1 hδ hδs hb.1 hθv0 hθv1 (by linarith) (by positivity) hL.2.1)
      (by exact_mod_cast hL.1) hLle hMlow hMw hkey
  -- the vertical height density
  set D := 24 * G.n * δ ^ 2 / θv ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  have hDbound : ∀ l u : ℝ, l ≤ u → heightMass Y' (Icc l u) ≤ ENNReal.ofReal (D * (u - l)) := by
    intro l u hlu
    rw [heightMass_eq_shading Y' measurableSet_Icc, ENNReal.ofReal_mul hD0]
    exact Reg.vertical_shadingHeightMeasure hδ hθv0 hθv1 hS.v_unit hY'm hS.sub_tube
      (fun i => by
        by_cases h : Y' i = ∅
        · exact Or.inl h
        · exact Or.inr (hS.vert i (Set.nonempty_iff_ne_empty.mpr h))) l u
  have hDsmall : 20 * D * Real.sqrt ρ ≤ M / 4 := by
    have hsqρ : Real.sqrt ρ ≤ δ ^ (κ' / 2) := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_one_div κ' 2, Real.rpow_mul hδ.le]
      exact Real.rpow_le_rpow hρpos.le hρκ2 (by norm_num)
    have e : 20 * D * δ ^ (κ' / 2) =
        (1920 * δ ^ (κ' / 2 - 2 * εv - ε₁)) * (δ ^ ε₁ * G.n * δ ^ 2) / 4 := by
      rw [hD, hθv]
      have e2 : δ ^ (κ' / 2) = δ ^ (κ' / 2 - 2 * εv - ε₁) * (δ ^ εv) ^ 2 * δ ^ ε₁ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1; push_cast; ring
      rw [e2]
      field_simp
      ring
    have hDs : 20 * D * Real.sqrt ρ ≤ 20 * D * δ ^ (κ' / 2) :=
      mul_le_mul_of_nonneg_left hsqρ (by positivity)
    have hp : 0 ≤ δ ^ ε₁ * G.n * δ ^ 2 := by positivity
    calc 20 * D * Real.sqrt ρ ≤ 20 * D * δ ^ (κ' / 2) := hDs
      _ = (1920 * δ ^ (κ' / 2 - 2 * εv - ε₁)) * (δ ^ ε₁ * G.n * δ ^ 2) / 4 := e
      _ ≤ 1 * (δ ^ ε₁ * G.n * δ ^ 2) / 4 := by gcongr
      _ ≤ M / 4 := by linarith
  -- all cells
  obtain ⟨J, a', b', hfit⟩ := cells_assemble hS hspec hsρ₀ hs8 hK hθη (by positivity) hn
    hρ1' (by linarith) hheavy hD0 hDbound hDsmall
  refine ⟨J, a', b', ?_⟩
  -- the final comparison of masses
  have hYfin : ∑ i, volume (Y i) ≠ ∞ := by
    apply ne_of_lt; apply ENNReal.sum_lt_top.mpr; intro i _
    exact (measure_mono ((hYext.1.2.2.2.2.2.1 i).trans (hYext.1.2.2.1 i))).trans_lt
      measure_ball_lt_top
  have hS384 : (∑ i, volume (Y i)).toReal ≤ 384 * G.n * δ ^ 2 := by
    have : ∑ i, volume (Y i) ≤ ENNReal.ofReal (384 * G.n * δ ^ 2) := by
      calc ∑ i, volume (Y i) ≤ ∑ _i : Fin G.n, ENNReal.ofReal (384 * δ ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            exact (measure_mono (hYext.1.2.2.2.2.2.1 i)).trans
              (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ hδ1 _ _
                (hYext.1.2.1 i))
        _ = ENNReal.ofReal (384 * G.n * δ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              show 384 * (G.n : ℝ) * δ ^ 2 = (G.n : ℝ) * (384 * δ ^ 2) by ring,
              ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hmass := final_mass (εl := εl) (ε₁ := ε₁) (ε := ε) hδ hρpos hs_pos hεl0.le hnr.le
    hS384 hMlow hs_ge hs_ge2 c12
  calc ENNReal.ofReal (δ ^ ε) * (∑ i, volume (Y i))
      = ENNReal.ofReal (δ ^ ε * (∑ i, volume (Y i)).toReal) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ENNReal.ofReal_toReal hYfin]
    _ ≤ ENNReal.ofReal (s ^ εl * Real.sqrt s / (24 * Real.sqrt ρ) * M) :=
        ENNReal.ofReal_le_ofReal hmass
    _ ≤ Reg.shadingHeightMeasure Y' (⋃ j ∈ J, Reg.affineFitHeights G.f (Real.sqrt ρ) ρ j
          (a' j) (b' j)) := hfit
    _ ≤ _ := shadingHeightMeasure_mono (fun i => (hY'Z i).trans (hZY i)) _

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
