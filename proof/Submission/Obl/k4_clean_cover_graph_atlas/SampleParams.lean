-- Adapted from LOT tree g-oai-074, obligation o194, session x0672,
-- commit 29e2793f, Submission/Obl/k4_greedy_cover_graph_atlas/SampleParams.lean.
import Submission.Obl.k4_clean_cover_graph_atlas.SampleScales
import Submission.Obl.k4_clean_cover_graph_atlas.Prepare

/-!
# The numerical hypotheses of the concrete sample assembly

Each lemma here supplies one numerical hypothesis of the concrete finite sample assembly
(`coreOutput_of_sample_data`, o210/x0719) in exactly its displayed form, from the scales of
`SampleScales`: the fine and old fits `η_fine = N^Σ δ(r₀+hL) A^(Cs+1)`, `η_old = κ δ(r₀) A^(Cs+1)`,
the comparison ratio `R = δ(r₀)/δ(r₀+hL)` and spread unit `M = δ(r₀)`.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_clean_cover_graph_atlas

open Submission.Lib.K4XInterface

theorem gδ_le_one {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) : δ N r ≤ 1 := by
  have h0 : δ N 0 = 1 := by
    show (2 : ℝ) ^ (-(⌊0 * Real.log N / Real.log 2⌋ : ℤ)) = 1
    simp
  calc δ N r ≤ δ N 0 := delta_antitone hN hr
    _ = 1 := h0

theorem one_le_cmpRatio {N r₀ hL : ℝ} (hN : 1 ≤ N) (hhL : 0 ≤ hL) : 1 ≤ cmpRatio N r₀ hL := by
  unfold cmpRatio
  rw [le_div_iff₀ (gδ_pos N (r₀ + hL)), one_mul]
  exact delta_antitone hN (by linarith)

/-- `η_fine + η_old ≤ M · fitFactor`. -/
theorem fits_le_spread {N U κ A r₀ hL : ℝ} {Cs : ℕ} (hN : 1 ≤ N) (hhL : 0 ≤ hL)
    (hU : 0 ≤ U) (hκ : 0 ≤ κ) (hA : 0 ≤ A) :
    U * δ N (r₀ + hL) * A ^ ((Cs : ℝ) + 1) + κ * δ N r₀ * A ^ ((Cs : ℝ) + 1) ≤
      δ N r₀ * fitFactor A U κ Cs := by
  have hδ : δ N (r₀ + hL) ≤ δ N r₀ := delta_antitone hN (by linarith)
  have hAp : 0 ≤ A ^ ((Cs : ℝ) + 1) := Real.rpow_nonneg hA _
  unfold fitFactor
  nlinarith [mul_nonneg hU hAp]

/-- **`hremez`** of the concrete assembly. -/
theorem sample_hremez {Kd Cd Krem Crem N U κ S r₀ h L gain εG : ℝ} {Cs : ℕ}
    (hN : 1 ≤ N) (hS : 0 ≤ S) (hKd : 0 ≤ Kd) (hCd : 0 ≤ Cd) (hKrem : 1 ≤ Krem) (hCrem : 1 ≤ Crem)
    (hU0 : 0 ≤ U) (hU : U ≤ N ^ (4 * S)) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ S)
    (hεG : 0 < εG) (hεG1 : εG ≤ 1) (hgain : 0 < gain) (hL : 0 < L) (hgh : gain ≤ h)
    (hbud : expMult Cs Cd Crem * S ≤ εG * gain * L / 8)
    (hNξ : (2 * (2 * Krem * Crem * 2 ^ (30 * Crem) * scaleConst Kd Cd ^ ((Cs : ℝ) + 1))) ^
      (1 / (εG * gain * L / 2)) ≤ N) :
    Krem * (Crem * groupFloor N S ^ (-Crem) *
      (U * δ N (r₀ + h * L) * sheetScale Kd Cd N U κ S ^ ((Cs : ℝ) + 1) +
        κ * δ N r₀ * sheetScale Kd Cd N U κ S ^ ((Cs : ℝ) + 1))) ≤
      δ N r₀ * cmpRatio N r₀ (h * L) ^ εG := by
  have hN0 : 0 < N := by linarith
  have hA0 : 0 ≤ sheetScale Kd Cd N U κ S := by
    have := (sheetScale_ge (S := S) hN0 hKd hCd hU0 hκ0).2.2.2.1; linarith
  have hfit := fits_le_spread (Cs := Cs) (r₀ := r₀) (hL := h * L) hN
    (mul_nonneg (by linarith) hL.le) hU0 hκ0 hA0
  have hband := group_band_numeric (r₀ := r₀) hN hS hKd hCd hKrem hCrem hU0 hU hκ0 hκ hεG hεG1
    hgain hL hgh hbud hNξ
  exact group_band (gδ_pos N r₀).le (by linarith) (by linarith) (groupFloor_pos hN0 S) hfit hband

/-- **`hwidth`** of the concrete assembly. -/
theorem sample_hwidth {Kd Cd Crem N U κ S r₀ h L gain εG : ℝ} {Cs : ℕ}
    (hN : 1 ≤ N) (hS : 0 ≤ S) (hKd : 0 ≤ Kd) (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem)
    (hU1 : 1 ≤ U) (hU : U ≤ N ^ (4 * S)) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ S)
    (hεG : 0 < εG) (hεG1 : εG ≤ 1) (hgain : 0 < gain) (hL : 0 < L) (hgh : gain ≤ h)
    (hrL : r₀ + h * L ≤ L)
    (hbud : expMult Cs Cd Crem * S ≤ εG * gain * L / 8)
    (hNξ : (2 * (6 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1))) ^ (1 / (εG * gain * L / 2)) ≤ N) :
    2 * (U * δ N (r₀ + h * L) * sheetScale Kd Cd N U κ S ^ ((Cs : ℝ) + 1)) + δ N L ≤
      δ N r₀ * cmpRatio N r₀ (h * L) ^ (-1 + εG) := by
  have hN0 : 0 < N := by linarith
  set A := sheetScale Kd Cd N U κ S
  have hA2 : 2 ≤ A := (sheetScale_ge (S := S) hN0 hKd hCd (by linarith) hκ0).2.2.2.1
  have hAp : 1 ≤ A ^ ((Cs : ℝ) + 1) := Real.one_le_rpow (by linarith) (by positivity)
  have hX1 : 1 ≤ U * A ^ ((Cs : ℝ) + 1) := by nlinarith
  have hXf : U * A ^ ((Cs : ℝ) + 1) ≤ fitFactor A U κ Cs := by
    unfold fitFactor; nlinarith [Real.rpow_nonneg (show (0:ℝ) ≤ A by linarith) ((Cs : ℝ) + 1)]
  have hw := group_width_numeric (r₀ := r₀) (Cs := Cs) hN hS hKd hCd hCrem (by linarith) hU hκ0 hκ
    hεG hεG1 hgain hL hgh hbud hNξ
  have hδL : δ N L ≤ δ N (r₀ + h * L) := delta_antitone hN hrL
  have := group_width (r₀ := r₀) (hL := h * L) (ε := εG) (gδ_pos N L).le hδL hX1
    (by linarith)
  calc 2 * (U * δ N (r₀ + h * L) * A ^ ((Cs : ℝ) + 1)) + δ N L
      = 2 * (δ N (r₀ + h * L) * (U * A ^ ((Cs : ℝ) + 1))) + δ N L := by ring
    _ ≤ _ := this

/-- **`hthr`** of the concrete assembly: `340 (η_fine + Σ width / lower) ≤ δ(r₀) N^(-θ h L)`. -/
theorem sample_hthr {Kd Cd Crem N U κ S r₀ h L gain εG θo lower : ℝ} {Cs : ℕ} {ι : Type*}
    [Fintype ι] (upper : ι → ℝ)
    (hN : 1 ≤ N) (hS : 0 ≤ S) (hKd : 0 ≤ Kd) (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem)
    (hU0 : 0 ≤ U) (hU : U ≤ N ^ (4 * S)) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ S)
    (hεG : 0 < εG) (hεG2 : εG ≤ 1 / 2) (hθ0 : 0 ≤ θo) (hθ : θo ≤ εG / 4)
    (hgain : 0 < gain) (hL : 0 < L) (hgh : gain ≤ h) (hup : ∀ i, 0 ≤ upper i)
    (hlower : 0 < lower)
    (hbud : expMult Cs Cd Crem * S ≤ εG * gain * L / 8)
    (hN1 : (2720 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1)) ^ (1 / (gain * L / 2)) ≤ N)
    (hN2 : (1360 * (∑ i, upper i) / lower + 1) ^ (1 / (εG * gain * L / 2)) ≤ N) :
    340 * (U * δ N (r₀ + h * L) * sheetScale Kd Cd N U κ S ^ ((Cs : ℝ) + 1) +
      (∑ i, upper i * (δ N r₀ * cmpRatio N r₀ (h * L) ^ (-εG))) / lower) ≤
      δ N r₀ * N ^ (-(θo * h * L)) := by
  have hN0 : 0 < N := by linarith
  set A := sheetScale Kd Cd N U κ S
  have hA0 : 0 ≤ A := by have := (sheetScale_ge (S := S) hN0 hKd hCd hU0 hκ0).2.2.2.1; linarith
  have hJ : 0 ≤ ∑ i, upper i := Finset.sum_nonneg fun i _ => hup i
  have hroot := group_root_numeric (r₀ := r₀) (Cs := Cs) hN hS hKd hCd hCrem hU0 hU hκ0 hκ hεG
    hεG2 hθ0 hθ hgain hL hgh hJ hlower hbud hN1 hN2
  have htarget := group_root_target (r₀ := r₀) (hL := h * L) (X := fitFactor A U κ Cs) hlower hroot
  have hXf : U * A ^ ((Cs : ℝ) + 1) ≤ fitFactor A U κ Cs := by
    unfold fitFactor; nlinarith [Real.rpow_nonneg hA0 ((Cs : ℝ) + 1)]
  have hsum : (∑ i, upper i * (δ N r₀ * cmpRatio N r₀ (h * L) ^ (-εG))) =
      (∑ i, upper i) * (δ N r₀ * cmpRatio N r₀ (h * L) ^ (-εG)) := by
    rw [Finset.sum_mul]
  rw [hsum, show θo * h * L = θo * (h * L) by ring]
  have hδ1 := gδ_pos N (r₀ + h * L)
  calc 340 * (U * δ N (r₀ + h * L) * A ^ ((Cs : ℝ) + 1) +
        (∑ i, upper i) * (δ N r₀ * cmpRatio N r₀ (h * L) ^ (-εG)) / lower)
      ≤ 340 * (δ N (r₀ + h * L) * fitFactor A U κ Cs +
        (∑ i, upper i) * (δ N r₀ * cmpRatio N r₀ (h * L) ^ (-εG)) / lower) := by
        have : U * δ N (r₀ + h * L) * A ^ ((Cs : ℝ) + 1) ≤ δ N (r₀ + h * L) * fitFactor A U κ Cs := by
          nlinarith
        linarith
    _ ≤ _ := htarget

/-- **`hcount`** with a factor `2` (two derivative-sign bits per greedy entry). -/
theorem sample_hcount {Cs : ℕ} {Cd Crem N ρ gain L ε σ τ h d₁ εG n r₀ : ℝ}
    (hN : 1 ≤ N) (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem) (hρ : 0 ≤ ρ) (hgain : 0 < gain) (hL : 0 < L)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hgh : gain ≤ h) (hd₁ : 0 ≤ d₁)
    (hεG : 0 < εG) (hdε : d₁ + εG ≤ 1)
    (hbud : expMult Cs Cd Crem * slackTot ρ gain L ε σ τ ≤ εG * gain * L / 8)
    (hN2 : (2 : ℝ) ^ (1 / (εG * gain * L / 4)) ≤ N)
    (hn : n ≤ 2 * N ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε)) :
    n ≤ cmpRatio N r₀ (h * L) ^ (d₁ + εG) := by
  have hN0 : 0 < N := by linarith
  have hξ : 0 < εG * gain * L / 4 := by positivity
  have h2 : (2 : ℝ) * N ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε) ≤
      N ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε + εG * gain * L / 4) :=
    rpow_absorb hN (by norm_num) hξ hN2 le_rfl
  have hS0 : 0 ≤ slackTot ρ gain L ε σ τ := by unfold slackTot; positivity
  have hsm := slack_small hCd hCrem hS0 hbud
  have hgs : greedySlack ρ gain L ε ≤ 4 * slackTot ρ gain L ε σ τ :=
    greedySlack_le (by positivity) hε hσ hτ
  have hhL : 0 ≤ h * L := mul_nonneg (by linarith) hL.le
  have hgL : εG * gain * L ≤ εG * (h * L) := by
    have := mul_le_mul_of_nonneg_right hgh hL.le; nlinarith
  refine group_count hN hεG.le hd₁ hdε hhL hξ hN2 (hn.trans h2) ?_
  unfold greedySlack at hgs
  nlinarith

/-- The time exponent and the scale exponent. -/
noncomputable def timeExp (κ₁ θ gain L : ℝ) : ℕ := ⌈κ₁ * θ * gain * L / 8⌉₊

noncomputable def scaleExp (Kd Cd ϖ gain L : ℝ) : ℕ :=
  ⌈scaleConst Kd Cd⌉₊ + ⌈(25 * Cd + 8) * (2 * ϖ * gain * L)⌉₊

/-- **The complexity exponent `Mc`.** -/
noncomputable def coreExp (Mg Mpr : ℕ) (Kd Cd ϖ gain L κ₁ θ : ℝ) : ℕ :=
  Mg + 3 * Mpr + 20 * scaleExp Kd Cd ϖ gain L + 3 * timeExp κ₁ θ gain L + 20

theorem le_two_pow_ceil {x : ℝ} (hx : 0 ≤ x) : x ≤ (2 : ℝ) ^ ⌈x⌉₊ := by
  have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h2 : (⌈x⌉₊ : ℝ) ≤ (2 : ℝ) ^ ⌈x⌉₊ := by
    exact_mod_cast (Nat.lt_two_pow_self).le
  linarith

/-- The sheet scale is a fixed power of `N`, with exponent `scaleExp` (chosen before `β`). -/
theorem sheetScale_le_pow {Kd Cd N U κ S ϖ gain L : ℝ} (hN : 2 ≤ N) (hS : 0 ≤ S)
    (hSϖ : S ≤ 2 * ϖ * gain * L) (hKd : 0 ≤ Kd) (hCd : 0 ≤ Cd) (hU0 : 0 ≤ U)
    (hU : U ≤ N ^ (4 * S)) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ S) :
    sheetScale Kd Cd N U κ S ≤ N ^ scaleExp Kd Cd ϖ gain L := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hA := sheetScale_le hN1 hS hKd hCd hU0 hU hκ0 hκ
  have hc : scaleConst Kd Cd ≤ N ^ ⌈scaleConst Kd Cd⌉₊ :=
    (le_two_pow_ceil (by linarith [one_le_scaleConst hKd hCd])).trans
      (pow_le_pow_left₀ (by norm_num) hN _)
  have he : N ^ ((25 * Cd + 8) * S) ≤ N ^ ⌈(25 * Cd + 8) * (2 * ϖ * gain * L)⌉₊ := by
    rw [← Real.rpow_natCast]
    exact rpow_mono_exp hN1 ((mul_le_mul_of_nonneg_left hSϖ (by positivity)).trans
      (Nat.le_ceil _))
  calc sheetScale Kd Cd N U κ S ≤ scaleConst Kd Cd * N ^ ((25 * Cd + 8) * S) := hA
    _ ≤ N ^ ⌈scaleConst Kd Cd⌉₊ * N ^ ⌈(25 * Cd + 8) * (2 * ϖ * gain * L)⌉₊ :=
        mul_le_mul hc he (by positivity) (by positivity)
    _ = N ^ scaleExp Kd Cd ϖ gain L := by unfold scaleExp; rw [pow_add]

/-- **`hsourceBudget`, `hscaleBudget`, `hinverseBudget`** of the concrete assembly. -/
theorem sample_budgets {N A Bw η : ℝ} {Mg Mpr sE tE : ℕ} (hN : 2 ≤ N) (hA1 : 1 ≤ A)
    (hA : A ≤ N ^ sE) (hB : 0 < Bw) (hBM : Bw ≤ N ^ Mpr) (hBi : Bw⁻¹ ≤ N ^ Mpr)
    (hη0 : 0 ≤ η) (hη : 340 * η ≤ 1) :
    8 * N ^ Mg ≤ N ^ (Mg + 3 * Mpr + 20 * sE + 3 * tE + 20) ∧
    Bw * A + 4 * N ^ Mg ≤ N ^ (Mg + 3 * Mpr + 20 * sE + 3 * tE + 20) ∧
    (1 + 80 * (η / Bw)) * (A / Bw + A ^ (20 : ℕ) / Bw ^ 2) ≤
      N ^ (Mg + 3 * Mpr + 20 * sE + 3 * tE + 20) := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  set Mc := Mg + 3 * Mpr + 20 * sE + 3 * tE + 20
  have hp : ∀ a b : ℕ, a ≤ b → N ^ a ≤ N ^ b := fun a b hab => pow_le_pow_right₀ hN1 hab
  have h8 : (8 : ℝ) ≤ N ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hN 3]
  have hpos : ∀ k : ℕ, 0 < N ^ k := fun k => pow_pos hN0 k
  refine ⟨?_, ?_, ?_⟩
  · calc 8 * N ^ Mg ≤ N ^ 3 * N ^ Mg := mul_le_mul_of_nonneg_right h8 (hpos _).le
      _ = N ^ (Mg + 3) := by rw [← pow_add, add_comm]
      _ ≤ N ^ Mc := hp _ _ (by omega)
  · have h1 : Bw * A ≤ N ^ (Mpr + sE) := by
      rw [pow_add]; exact mul_le_mul hBM hA (by linarith) (hpos _).le
    have h2 : N ^ (Mpr + sE) ≤ N ^ (Mc - 1) := hp _ _ (by omega)
    have h3 : 4 * N ^ Mg ≤ N ^ (Mc - 1) := by
      have : 4 * N ^ Mg ≤ N ^ (Mg + 2) := by
        rw [pow_add]; nlinarith [hpos Mg, pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 2]
      exact this.trans (hp _ _ (by omega))
    have h4 : 2 * N ^ (Mc - 1) ≤ N ^ Mc := by
      have e : N ^ Mc = N ^ (Mc - 1) * N := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [e]; nlinarith [hpos (Mc - 1)]
    linarith
  · have hηB : 80 * (η / Bw) ≤ N ^ Mpr := by
      have h1 : η / Bw ≤ Bw⁻¹ / 340 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have := inv_pos.mpr hB
        nlinarith
      have h2 : Bw⁻¹ / 340 * 80 ≤ Bw⁻¹ := by have := inv_pos.mpr hB; nlinarith
      nlinarith
    have hf1 : 1 + 80 * (η / Bw) ≤ 2 * N ^ Mpr := by
      have : (1 : ℝ) ≤ N ^ Mpr := one_le_pow₀ hN1
      linarith
    have hA20 : A ^ (20 : ℕ) ≤ N ^ (20 * sE) := by
      rw [mul_comm, pow_mul]; exact pow_le_pow_left₀ (by linarith) hA 20
    have hAA : A ≤ A ^ (20 : ℕ) := le_self_pow₀ hA1 (by norm_num)
    have hBi2 : (Bw ^ 2)⁻¹ ≤ N ^ (2 * Mpr) := by
      rw [← inv_pow, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (inv_nonneg.mpr hB.le) hBi 2
    have hBi' : Bw⁻¹ ≤ N ^ (2 * Mpr) := hBi.trans (hp _ _ (by omega))
    have t1 : A * Bw⁻¹ ≤ N ^ (20 * sE) * N ^ (2 * Mpr) :=
      mul_le_mul (hAA.trans hA20) hBi' (inv_nonneg.mpr hB.le) (hpos _).le
    have t2 : A ^ (20 : ℕ) * (Bw ^ 2)⁻¹ ≤ N ^ (20 * sE) * N ^ (2 * Mpr) :=
      mul_le_mul hA20 hBi2 (by positivity) (hpos _).le
    have hf2 : A / Bw + A ^ (20 : ℕ) / Bw ^ 2 ≤ 2 * (N ^ (2 * Mpr) * N ^ (20 * sE)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      linarith
    calc (1 + 80 * (η / Bw)) * (A / Bw + A ^ (20 : ℕ) / Bw ^ 2)
        ≤ (2 * N ^ Mpr) * (2 * (N ^ (2 * Mpr) * N ^ (20 * sE))) := by
          apply mul_le_mul hf1 hf2 (by positivity) (by positivity)
      _ = 4 * N ^ (3 * Mpr + 20 * sE) := by
          rw [show 3 * Mpr + 20 * sE = Mpr + (2 * Mpr + 20 * sE) by ring, pow_add, pow_add]
          ring
      _ ≤ N ^ 2 * N ^ (3 * Mpr + 20 * sE) := by
          nlinarith [hpos (3 * Mpr + 20 * sE), pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 2]
      _ = N ^ (3 * Mpr + 20 * sE + 2) := by rw [← pow_add, add_comm 2]
      _ ≤ N ^ Mc := hp _ _ (by omega)

/-- The box range at a sample. -/
noncomputable def boxRangeOf (κ : ℝ) (s₀ : ℕ) : ℕ := ⌈κ⌉₊ * 2 ^ s₀ + 1

/-- **Counts:** `2^s₀`, the box range and the number of entries are below `N^Mc`. -/
theorem sample_card_bounds {N κ : ℝ} {n s₀ Mg tE sE Mpr : ℕ} (hN : 2 ≤ N) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ N) (hn : (n : ℝ) ≤ N ^ Mg) (hs₀ : (2 : ℝ) ^ s₀ ≤ N ^ tE) :
    (2 : ℝ) ^ s₀ ≤ N ^ (Mg + 3 * Mpr + 20 * sE + 3 * tE + 20) ∧
    ((boxRangeOf κ s₀ : ℕ) : ℝ) ≤ N ^ (Mg + 3 * Mpr + 20 * sE + 3 * tE + 20) ∧
    (Fintype.card (Entry n s₀ (boxRangeOf κ s₀)) : ℝ) ≤
      N ^ (Mg + 3 * Mpr + 20 * sE + 3 * tE + 20) := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  set Mc := Mg + 3 * Mpr + 20 * sE + 3 * tE + 20
  have hp : ∀ a b : ℕ, a ≤ b → N ^ a ≤ N ^ b := fun a b hab => pow_le_pow_right₀ hN1 hab
  have hpos : ∀ k : ℕ, 0 < N ^ k := fun k => pow_pos hN0 k
  have hK : ((boxRangeOf κ s₀ : ℕ) : ℝ) ≤ 3 * N ^ (tE + 1) := by
    unfold boxRangeOf
    push_cast
    have hc : (⌈κ⌉₊ : ℝ) ≤ κ + 1 := (Nat.ceil_lt_add_one hκ0).le
    have h1 : (⌈κ⌉₊ : ℝ) * 2 ^ s₀ ≤ (N + 1) * N ^ tE :=
      mul_le_mul (by linarith) hs₀ (by positivity) (by positivity)
    have h2 : (N + 1) * N ^ tE ≤ 2 * N ^ (tE + 1) := by
      rw [pow_succ]; nlinarith [hpos tE]
    have h3 : (1 : ℝ) ≤ N ^ (tE + 1) := one_le_pow₀ hN1
    linarith
  refine ⟨hs₀.trans (hp _ _ (by omega)), hK.trans ?_, ?_⟩
  · have : 3 * N ^ (tE + 1) ≤ N ^ (tE + 3) := by
      have e : N ^ (tE + 3) = N ^ (tE + 1) * N ^ 2 := by rw [← pow_add]
      rw [e]
      nlinarith [hpos (tE + 1), pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 2]
    exact this.trans (hp _ _ (by omega))
  · rw [card_entry]
    push_cast
    have hK2 : (2 * ((boxRangeOf κ s₀ : ℕ) : ℝ) + 2) ^ 2 ≤ 64 * N ^ (2 * tE + 2) := by
      have h1 : 2 * ((boxRangeOf κ s₀ : ℕ) : ℝ) + 2 ≤ 8 * N ^ (tE + 1) := by
        have : (1 : ℝ) ≤ N ^ (tE + 1) := one_le_pow₀ hN1
        linarith
      calc (2 * ((boxRangeOf κ s₀ : ℕ) : ℝ) + 2) ^ 2 ≤ (8 * N ^ (tE + 1)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h1 2
        _ = 64 * N ^ (2 * tE + 2) := by rw [mul_pow, ← pow_mul]; ring_nf
    calc (n : ℝ) * (2 ^ s₀ * ((2 * ((boxRangeOf κ s₀ : ℕ) : ℝ) + 2) ^ 2 * 4))
        ≤ N ^ Mg * (N ^ tE * ((64 * N ^ (2 * tE + 2)) * 4)) := by gcongr
      _ = 256 * N ^ (Mg + 3 * tE + 2) := by
          rw [show Mg + 3 * tE + 2 = Mg + (tE + (2 * tE + 2)) by ring, pow_add, pow_add]; ring
      _ ≤ N ^ 8 * N ^ (Mg + 3 * tE + 2) := by
          have : (256 : ℝ) ≤ N ^ 8 := by
            have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 8; norm_num at this; linarith
          nlinarith [hpos (Mg + 3 * tE + 2)]
      _ = N ^ (Mg + 3 * tE + 10) := by rw [← pow_add]; ring_nf
      _ ≤ N ^ Mc := hp _ _ (by omega)

/-- **`htotal`** of the concrete assembly from the covered mass floor and the tails. -/
theorem sample_htotal {N β ε Rg εg K₀ b : ℝ} {Sμ SH : ENNReal}
    (hSμ : ENNReal.ofReal (N ^ (-ε) / 4) ≤ Sμ) (hSH : SH ≤ ENNReal.ofReal (K₀ * N ^ b))
    (hfinal : N ^ (-β) ≤ N ^ (-ε) / 16) (hmatch : Rg ^ (-εg) ≤ 1 / 64)
    (hpair : K₀ * N ^ b * Rg ^ (-(2 * εg)) ≤ N ^ (-ε) / 64) (hRg : 0 < Rg) (hK₀ : 0 ≤ K₀)
    (hN : 0 < N) :
    ENNReal.ofReal (N ^ (-β)) +
      (ENNReal.ofReal (Rg ^ (-εg)) * Sμ + ENNReal.ofReal (Rg ^ (-(2 * εg))) * SH) ≤ Sμ := by
  have hNε : 0 ≤ N ^ (-ε) := (Real.rpow_pos_of_pos hN _).le
  have h1 : ENNReal.ofReal (Rg ^ (-εg)) * Sμ ≤ ENNReal.ofReal (1 / 64) * Sμ :=
    mul_le_mul' (ENNReal.ofReal_le_ofReal hmatch) le_rfl
  have h2 : ENNReal.ofReal (Rg ^ (-(2 * εg))) * SH ≤ ENNReal.ofReal (N ^ (-ε) / 64) := by
    calc ENNReal.ofReal (Rg ^ (-(2 * εg))) * SH
        ≤ ENNReal.ofReal (Rg ^ (-(2 * εg))) * ENNReal.ofReal (K₀ * N ^ b) := mul_le_mul' le_rfl hSH
      _ = ENNReal.ofReal (Rg ^ (-(2 * εg)) * (K₀ * N ^ b)) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg hRg.le _)).symm
      _ ≤ ENNReal.ofReal (N ^ (-ε) / 64) := ENNReal.ofReal_le_ofReal (by nlinarith)
  have h3 : ENNReal.ofReal (N ^ (-β)) ≤ ENNReal.ofReal (N ^ (-ε) / 16) :=
    ENNReal.ofReal_le_ofReal hfinal
  have h4 : ENNReal.ofReal (N ^ (-ε) / 16) + ENNReal.ofReal (N ^ (-ε) / 64) ≤
      ENNReal.ofReal (5 / 16) * Sμ := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    calc ENNReal.ofReal (N ^ (-ε) / 16 + N ^ (-ε) / 64)
        = ENNReal.ofReal (5 / 16) * ENNReal.ofReal (N ^ (-ε) / 4) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
      _ ≤ ENNReal.ofReal (5 / 16) * Sμ := mul_le_mul' le_rfl hSμ
  calc ENNReal.ofReal (N ^ (-β)) +
        (ENNReal.ofReal (Rg ^ (-εg)) * Sμ + ENNReal.ofReal (Rg ^ (-(2 * εg))) * SH)
      ≤ ENNReal.ofReal (N ^ (-ε) / 16) +
        (ENNReal.ofReal (1 / 64) * Sμ + ENNReal.ofReal (N ^ (-ε) / 64)) := by
        gcongr
    _ = (ENNReal.ofReal (N ^ (-ε) / 16) + ENNReal.ofReal (N ^ (-ε) / 64)) +
        ENNReal.ofReal (1 / 64) * Sμ := by ring
    _ ≤ ENNReal.ofReal (5 / 16) * Sμ + ENNReal.ofReal (1 / 64) * Sμ := by gcongr
    _ = ENNReal.ofReal (21 / 64) * Sμ := by
        rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    _ ≤ 1 * Sμ := mul_le_mul' (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)) le_rfl
    _ = Sμ := one_mul Sμ

theorem error_budget_final16 {N ε β : ℝ} (hN : 1 ≤ N) (hβ : 0 < β) (hεβ : ε ≤ β / 2)
    (hN2 : (16 : ℝ) ^ (1 / (β / 2)) ≤ N) : N ^ (-β) ≤ N ^ (-ε) / 16 := by
  have h := rpow_absorb hN (by norm_num : (1 : ℝ) ≤ 16) (by positivity) hN2
    (show -β + β / 2 ≤ -ε by linarith)
  linarith

/-- **The late-sample threshold** of the concrete assembly: the maximum of every threshold used
by `subBlock_time_budget`, `sample_hwidth`, `sample_hremez`, `sample_hthr`, `sample_hcount`,
`group_radius_numeric`, `error_budget_match`, `error_budget_pair`, `error_budget_light`,
`error_budget_final16` and `list_budget`. -/
noncomputable def sampleN0 (Kd Cd Krem Crem : ℝ) (Cs : ℕ)
    (κ₁ θ gain L εG β τ radius Jsum lower K₀ : ℝ) (Clist : ℕ) : ℝ :=
  max 2 <| max ((2 * (1536 * scaleConst Kd Cd ^ (Cs : ℝ))) ^ (1 / (κ₁ * θ * gain * L / 16))) <|
  max ((2 * (6 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1))) ^ (1 / (εG * gain * L / 2))) <|
  max ((2 * (2 * Krem * Crem * 2 ^ (30 * Crem) * scaleConst Kd Cd ^ ((Cs : ℝ) + 1))) ^
    (1 / (εG * gain * L / 2))) <|
  max ((2720 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1)) ^ (1 / (gain * L / 2))) <|
  max ((1360 * Jsum / lower + 1) ^ (1 / (εG * gain * L / 2))) <|
  max ((2 : ℝ) ^ (1 / (εG * gain * L / 4))) <|
  max ((2 * radius + 1) ^ (1 / (gain * L))) <|
  max ((128 : ℝ) ^ (1 / (εG * gain * L / 2))) <|
  max ((256 * K₀ + 1) ^ (1 / (εG * gain * L / 2))) <|
  max ((256 : ℝ) ^ (1 / τ)) <|
  max ((16 : ℝ) ^ (1 / (β / 2))) ((100 * (Clist : ℝ) + 1) ^ (1 / (β / 4)))

theorem sampleN0_spec {Kd Cd Krem Crem : ℝ} {Cs : ℕ}
    {κ₁ θ gain L εG β τ radius Jsum lower K₀ : ℝ} {Clist : ℕ} {N : ℝ}
    (hN : sampleN0 Kd Cd Krem Crem Cs κ₁ θ gain L εG β τ radius Jsum lower K₀ Clist ≤ N) :
    2 ≤ N ∧
    (2 * (1536 * scaleConst Kd Cd ^ (Cs : ℝ))) ^ (1 / (κ₁ * θ * gain * L / 16)) ≤ N ∧
    (2 * (6 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1))) ^ (1 / (εG * gain * L / 2)) ≤ N ∧
    (2 * (2 * Krem * Crem * 2 ^ (30 * Crem) * scaleConst Kd Cd ^ ((Cs : ℝ) + 1))) ^
      (1 / (εG * gain * L / 2)) ≤ N ∧
    (2720 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1)) ^ (1 / (gain * L / 2)) ≤ N ∧
    (1360 * Jsum / lower + 1) ^ (1 / (εG * gain * L / 2)) ≤ N ∧
    (2 : ℝ) ^ (1 / (εG * gain * L / 4)) ≤ N ∧
    (2 * radius + 1) ^ (1 / (gain * L)) ≤ N ∧
    (128 : ℝ) ^ (1 / (εG * gain * L / 2)) ≤ N ∧
    (256 * K₀ + 1) ^ (1 / (εG * gain * L / 2)) ≤ N ∧
    (256 : ℝ) ^ (1 / τ) ≤ N ∧
    (16 : ℝ) ^ (1 / (β / 2)) ≤ N ∧
    (100 * (Clist : ℝ) + 1) ^ (1 / (β / 4)) ≤ N := by
  unfold sampleN0 at hN
  simp only [max_le_iff] at hN
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hN
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end Submission.Obl.k4_clean_cover_graph_atlas
