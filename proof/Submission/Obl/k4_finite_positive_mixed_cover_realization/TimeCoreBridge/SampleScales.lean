-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/SampleScales.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from LOT tree g-oai-074, obligation o194, session x0672,
-- commit c10e54a1, Submission/Obl/k4_greedy_cover_graph_atlas/SampleScales.lean.
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GroupNumerics

/-!
# The scales of one sample

Concrete choices of the per-sample scales, as functions of the sample data and of the kernel
constants (`Kd`, `Cd` of the original discriminant bound; `Cs` of the classified sheet choice):

* `slackTot = ρ gain L + ε + σ + τ`, the total slack; the greedy slack `Σ = 4ρ gain L + 4ε` and
  `U = N^Σ`;
* `discFloor = N^(-25 slackTot) / 2^10`, a uniform lower bound for the relative projection mass
  of every retained entry in normalized packet coordinates;
* `sheetScale A = 4 (U + κ + 1) + 3 Kd Cd (U + κ)² discFloor^(-Cd)`, dominating the slopes of new
  and old tests and the discriminant bound;
* `sheetRadius r = A^(-Cs) / 128` and the sub-block exponent `s₀`, the least with
  `2^s₀ ≥ 256 (κ + 2) A^Cs` (so `side s₀ · (κ + 2) ≤ r / 2`).
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

/-- The total slack of a sample. -/
noncomputable def slackTot (ρ gain L ε σ τ : ℝ) : ℝ := ρ * gain * L + ε + σ + τ

/-- The greedy slack exponent `Σ = 4 ρ gain L + 4 ε`. -/
noncomputable def greedySlack (ρ gain L ε : ℝ) : ℝ := 4 * ρ * gain * L + 4 * ε

theorem greedySlack_le {ρ gain L ε σ τ : ℝ} (hρ : 0 ≤ ρ * gain * L) (hε : 0 ≤ ε) (hσ : 0 ≤ σ)
    (hτ : 0 ≤ τ) : greedySlack ρ gain L ε ≤ 4 * slackTot ρ gain L ε σ τ := by
  unfold greedySlack slackTot; nlinarith

/-- The uniform relative projection floor of retained entries. -/
noncomputable def discFloor (N S : ℝ) : ℝ := N ^ (-(25 * S)) / 2 ^ 10

/-- The common sheet scale. -/
noncomputable def sheetScale (Kd Cd N U κ S : ℝ) : ℝ :=
  4 * (U + κ + 1) + 3 * Kd * Cd * (U + κ) ^ 2 * discFloor N S ^ (-Cd)

/-- The comparison radius of the sheets. -/
noncomputable def sheetRadius (A : ℝ) (Cs : ℕ) : ℝ := A ^ (-(Cs : ℝ)) / 128

theorem discFloor_pos {N : ℝ} (hN : 0 < N) (S : ℝ) : 0 < discFloor N S := by
  unfold discFloor; positivity

theorem sheetScale_ge {Kd Cd N U κ S : ℝ} (hN : 0 < N) (hKd : 0 ≤ Kd) (hCd : 0 ≤ Cd)
    (hU : 0 ≤ U) (hκ : 0 ≤ κ) :
    4 * U ≤ sheetScale Kd Cd N U κ S ∧ 4 * κ ≤ sheetScale Kd Cd N U κ S ∧
      κ + 1 ≤ sheetScale Kd Cd N U κ S ∧ 2 ≤ sheetScale Kd Cd N U κ S ∧
      3 * Kd * Cd * (U + κ) ^ 2 * discFloor N S ^ (-Cd) ≤ sheetScale Kd Cd N U κ S := by
  have h0 : 0 ≤ 3 * Kd * Cd * (U + κ) ^ 2 * discFloor N S ^ (-Cd) := by
    have := Real.rpow_nonneg (discFloor_pos hN S).le (-Cd)
    positivity
  unfold sheetScale
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The sub-block exponent: least `s₀` with `2^s₀ ≥ 256 (κ + 2) A^Cs`. -/
theorem exists_subBlock_exponent {A κ : ℝ} (Cs : ℕ) (hA : 1 ≤ A) (hκ : 0 ≤ κ) :
    ∃ s₀ : ℕ, 256 * (κ + 2) * A ^ (Cs : ℝ) ≤ (2 : ℝ) ^ s₀ ∧
      (2 : ℝ) ^ s₀ ≤ 2 * (256 * (κ + 2) * A ^ (Cs : ℝ)) := by
  apply exists_two_pow_between
  have : 1 ≤ A ^ (Cs : ℝ) := Real.one_le_rpow hA (Nat.cast_nonneg _)
  nlinarith

/-- With `2^s₀ ≥ 256 (κ + 2) A^Cs`, the sub-box side satisfies `side s₀ (κ + 2) ≤ r / 2`. -/
theorem side_le_half_radius {A κ : ℝ} {Cs s₀ : ℕ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (hs₀ : 256 * (κ + 2) * A ^ (Cs : ℝ) ≤ (2 : ℝ) ^ s₀) :
    side s₀ * (κ + 2) ≤ sheetRadius A Cs / 2 := by
  unfold side sheetRadius
  have hAC : 0 < A ^ (Cs : ℝ) := Real.rpow_pos_of_pos hA _
  have h2 : (0 : ℝ) < 2 ^ s₀ := by positivity
  rw [Real.rpow_neg hA.le]
  rw [inv_mul_le_iff₀ h2]
  have hinv : A ^ (Cs : ℝ) * (A ^ (Cs : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hAC.ne'
  have : (κ + 2) ≤ 2 ^ s₀ * ((A ^ (Cs : ℝ))⁻¹ / 128 / 2) := by
    rw [show 2 ^ s₀ * ((A ^ (Cs : ℝ))⁻¹ / 128 / 2) = 2 ^ s₀ / (256 * A ^ (Cs : ℝ)) by
      field_simp; norm_num]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  exact this

/-- `N^a ≤ N^b` for `a ≤ b`, `N ≥ 1`. -/
theorem rpow_mono_exp {N a b : ℝ} (hN : 1 ≤ N) (hab : a ≤ b) : N ^ a ≤ N ^ b :=
  Real.rpow_le_rpow_of_exponent_le hN hab

/-- The constant of the sheet scale bound. -/
noncomputable def scaleConst (Kd Cd : ℝ) : ℝ := 12 + 12 * Kd * Cd * 2 ^ (10 * Cd)

/-- **The sheet scale is a slack power.** -/
theorem sheetScale_le {Kd Cd N U κ S : ℝ} (hN : 1 ≤ N) (hS : 0 ≤ S) (hKd : 0 ≤ Kd)
    (hCd : 0 ≤ Cd) (hU0 : 0 ≤ U) (hU : U ≤ N ^ (4 * S)) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ S) :
    sheetScale Kd Cd N U κ S ≤ scaleConst Kd Cd * N ^ ((25 * Cd + 8) * S) := by
  have hN0 : 0 < N := by linarith
  have hS4 : N ^ S ≤ N ^ (4 * S) := rpow_mono_exp hN (by linarith)
  have h1 : (1 : ℝ) ≤ N ^ (4 * S) := Real.one_le_rpow hN (by linarith)
  have hUκ : U + κ ≤ 2 * N ^ (4 * S) := by linarith
  have hUκ1 : U + κ + 1 ≤ 3 * N ^ (4 * S) := by linarith
  have hsq : (U + κ) ^ 2 ≤ 4 * N ^ (8 * S) := by
    have h := pow_le_pow_left₀ (by linarith) hUκ 2
    have e1 : (N ^ (4 * S)) ^ (2 : ℕ) = N ^ (8 * S) := by
      rw [← Real.rpow_natCast (N ^ (4 * S)) 2, ← Real.rpow_mul hN0.le]
      congr 1; push_cast; ring
    have e : (2 * N ^ (4 * S)) ^ 2 = 4 * N ^ (8 * S) := by rw [mul_pow, e1]; norm_num
    linarith
  have hfl : discFloor N S ^ (-Cd) = 2 ^ (10 * Cd) * N ^ (25 * Cd * S) := by
    unfold discFloor
    rw [Real.div_rpow (Real.rpow_nonneg hN0.le _) (by positivity), ← Real.rpow_mul hN0.le]
    have h2 : ((2 : ℝ) ^ (10 : ℕ)) ^ (-Cd) = (2 : ℝ) ^ (-(10 * Cd)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; ring_nf
    rw [h2, Real.rpow_neg (by norm_num), div_inv_eq_mul,
      show -(25 * S) * -Cd = 25 * Cd * S by ring]
    ring
  have e8 : N ^ (8 * S) * N ^ (25 * Cd * S) = N ^ ((25 * Cd + 8) * S) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have h4le : N ^ (4 * S) ≤ N ^ ((25 * Cd + 8) * S) := rpow_mono_exp hN (by nlinarith)
  unfold sheetScale scaleConst
  rw [hfl]
  have hpow0 : 0 ≤ (2 : ℝ) ^ (10 * Cd) := by positivity
  calc 4 * (U + κ + 1) + 3 * Kd * Cd * (U + κ) ^ 2 * (2 ^ (10 * Cd) * N ^ (25 * Cd * S))
      ≤ 4 * (3 * N ^ (4 * S)) + 3 * Kd * Cd * (4 * N ^ (8 * S)) *
          (2 ^ (10 * Cd) * N ^ (25 * Cd * S)) := by
        gcongr
    _ = 12 * N ^ (4 * S) + 12 * Kd * Cd * 2 ^ (10 * Cd) * (N ^ (8 * S) * N ^ (25 * Cd * S)) := by
        ring
    _ = 12 * N ^ (4 * S) + 12 * Kd * Cd * 2 ^ (10 * Cd) * N ^ ((25 * Cd + 8) * S) := by
        rw [e8]
    _ ≤ 12 * N ^ ((25 * Cd + 8) * S) + 12 * Kd * Cd * 2 ^ (10 * Cd) * N ^ ((25 * Cd + 8) * S) := by
        gcongr
    _ = _ := by ring

/-- The matching exponent actually used: the kernel's, at most `(1 - d₁)/2` and `1/2`. -/
noncomputable def matchExp (εk d₁ : ℝ) : ℝ := min εk (min ((1 - d₁) / 2) (1 / 2))

theorem matchExp_pos {εk d₁ : ℝ} (hεk : 0 < εk) (hd₁ : d₁ < 1) : 0 < matchExp εk d₁ :=
  lt_min hεk (lt_min (by linarith) (by norm_num))

theorem matchExp_le (εk : ℝ) {d₁ : ℝ} (hd₁ : d₁ ≤ 1) :
    matchExp εk d₁ ≤ εk ∧ d₁ + matchExp εk d₁ ≤ 1 ∧ matchExp εk d₁ ≤ 1 / 2 := by
  unfold matchExp
  refine ⟨min_le_left _ _, ?_, (min_le_right _ _).trans (min_le_right _ _)⟩
  have : min εk (min ((1 - d₁) / 2) (1 / 2)) ≤ (1 - d₁) / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  linarith

/-- The exponent multiplier of the construction. -/
noncomputable def expMult (Cs : ℕ) (Cd Crem : ℝ) : ℝ :=
  4 * ((Cs + 2) * (25 * Cd + 8) + 30 * Crem + 40)

theorem expMult_pos {Cs : ℕ} {Cd Crem : ℝ} (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem) :
    0 < expMult Cs Cd Crem := by
  unfold expMult; positivity

/-- **The slack budget.** With `ρ ≤ ϖ` and `ε + σ + τ ≤ ϖ gain L`, every slack exponent times
the multiplier stays below one eighth of both the matching and the short-time budgets. -/
theorem slack_budget {εG κ₁ θ Λ ρ gain L ε σ τ : ℝ} (hΛ : 0 < Λ)
    (hρ : ρ ≤ varpiOf εG κ₁ θ Λ) (hgain : 0 < gain) (hL : 0 < L)
    (hsum : ε + σ + τ ≤ varpiOf εG κ₁ θ Λ * gain * L) :
    Λ * slackTot ρ gain L ε σ τ ≤ εG * gain * L / 8 ∧
      Λ * slackTot ρ gain L ε σ τ ≤ κ₁ * θ * gain * L / 8 := by
  have hgL : 0 < gain * L := mul_pos hgain hL
  have hS : slackTot ρ gain L ε σ τ ≤ 2 * (varpiOf εG κ₁ θ Λ * gain * L) := by
    unfold slackTot
    have : ρ * gain * L ≤ varpiOf εG κ₁ θ Λ * gain * L := by
      have := mul_le_mul_of_nonneg_right hρ hgL.le
      linarith [mul_assoc ρ gain L, mul_assoc (varpiOf εG κ₁ θ Λ) gain L]
    linarith
  have h1 := varpiOf_mul_le_eps (εm := εG) (κ₁ := κ₁) (θ := θ) hΛ
  have h2 := varpiOf_mul_le_time (εm := εG) (κ₁ := κ₁) (θ := θ) hΛ
  have hΛS : Λ * slackTot ρ gain L ε σ τ ≤ 2 * (Λ * varpiOf εG κ₁ θ Λ) * (gain * L) := by
    have := mul_le_mul_of_nonneg_left hS hΛ.le
    linarith [show Λ * (2 * (varpiOf εG κ₁ θ Λ * gain * L)) =
      2 * (Λ * varpiOf εG κ₁ θ Λ) * (gain * L) by ring]
  constructor
  · have : 2 * (Λ * varpiOf εG κ₁ θ Λ) ≤ εG / 8 := by linarith
    nlinarith
  · have : 2 * (Λ * varpiOf εG κ₁ θ Λ) ≤ κ₁ * θ / 8 := by linarith
    nlinarith

/-- `(K N^a)^p ≤ K^p N^(p a)` for the real power `p ≥ 0`. -/
theorem mul_rpow_le_of_le {N K A a p : ℝ} (hN : 0 < N) (hK : 0 ≤ K) (hA0 : 0 ≤ A)
    (hA : A ≤ K * N ^ a) (hp : 0 ≤ p) : A ^ p ≤ K ^ p * N ^ (p * a) := by
  calc A ^ p ≤ (K * N ^ a) ^ p := Real.rpow_le_rpow hA0 hA hp
    _ = K ^ p * N ^ (p * a) := by
        rw [Real.mul_rpow hK (by positivity), ← Real.rpow_mul hN.le, mul_comm a p]

/-- **The short-time budget.** The sub-block count fits `N^(κ₁ θ gain L / 8)`. -/
theorem subBlock_time_budget {Kd Cd N U κ S κ₁ θ gain L Λ : ℝ} {Cs s₀ : ℕ}
    (hN : 1 ≤ N) (hS : 0 ≤ S) (hKd : 0 ≤ Kd) (hCd : 0 ≤ Cd) (hU0 : 0 ≤ U) (hU : U ≤ N ^ (4 * S))
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ S)
    (hΛ : 4 * ((Cs : ℝ) * (25 * Cd + 8) + 1) ≤ Λ) (hbud : Λ * S ≤ κ₁ * θ * gain * L / 8)
    (hξ : 0 < κ₁ * θ * gain * L)
    (hNξ : (2 * (1536 * scaleConst Kd Cd ^ (Cs : ℝ))) ^ (1 / (κ₁ * θ * gain * L / 16)) ≤ N)
    (hs₀ : (2 : ℝ) ^ s₀ ≤ 2 * (256 * (κ + 2) * sheetScale Kd Cd N U κ S ^ (Cs : ℝ))) :
    (2 : ℝ) ^ s₀ ≤ N ^ (κ₁ * θ * gain * L / 8) := by
  have hN0 : 0 < N := by linarith
  set A := sheetScale Kd Cd N U κ S
  have hA := sheetScale_le hN hS hKd hCd hU0 hU hκ0 hκ
  have hA0 : 0 ≤ A := by have := (sheetScale_ge (S := S) hN0 hKd hCd hU0 hκ0).2.2.2.1; linarith
  have hCA : 0 ≤ scaleConst Kd Cd := by unfold scaleConst; positivity
  have hAC := mul_rpow_le_of_le hN0 hCA hA0 hA (Nat.cast_nonneg Cs)
  have hκ2 : κ + 2 ≤ 3 * N ^ S := by
    have : 1 ≤ N ^ S := Real.one_le_rpow hN hS
    linarith
  have hX : 2 * (256 * (κ + 2) * A ^ (Cs : ℝ)) ≤
      1536 * scaleConst Kd Cd ^ (Cs : ℝ) * N ^ (((Cs : ℝ) * (25 * Cd + 8) + 1) * S) := by
    have e : N ^ (((Cs : ℝ) * (25 * Cd + 8) + 1) * S) =
        N ^ S * N ^ ((Cs : ℝ) * ((25 * Cd + 8) * S)) := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [e]
    have hK0 : 0 ≤ scaleConst Kd Cd ^ (Cs : ℝ) := Real.rpow_nonneg hCA _
    calc 2 * (256 * (κ + 2) * A ^ (Cs : ℝ)) ≤ 2 * (256 * (3 * N ^ S) *
          (scaleConst Kd Cd ^ (Cs : ℝ) * N ^ ((Cs : ℝ) * ((25 * Cd + 8) * S)))) := by
          gcongr
      _ = _ := by ring
  have hgap : ((Cs : ℝ) * (25 * Cd + 8) + 1) * S + κ₁ * θ * gain * L / 16 ≤
      κ₁ * θ * gain * L / 8 := by
    have : ((Cs : ℝ) * (25 * Cd + 8) + 1) * S ≤ Λ * S / 4 := by nlinarith
    linarith
  have hK1 : (1 : ℝ) ≤ 1536 * scaleConst Kd Cd ^ (Cs : ℝ) := by
    have : 1 ≤ scaleConst Kd Cd := by unfold scaleConst; nlinarith [Real.rpow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (10 * Cd), mul_nonneg hKd hCd]
    have := Real.one_le_rpow this (Nat.cast_nonneg Cs)
    linarith
  have habs := rpow_absorb hN (by linarith : (1 : ℝ) ≤ 2 * (1536 * scaleConst Kd Cd ^ (Cs : ℝ)))
    (by positivity : (0 : ℝ) < κ₁ * θ * gain * L / 16) hNξ hgap
  have : 1536 * scaleConst Kd Cd ^ (Cs : ℝ) * N ^ (((Cs : ℝ) * (25 * Cd + 8) + 1) * S) ≤
      N ^ (κ₁ * θ * gain * L / 8) := by
    have hp : 0 ≤ N ^ (((Cs : ℝ) * (25 * Cd + 8) + 1) * S) := by positivity
    nlinarith
  linarith

/-- The fit factor `(U + κ) A^(Cs+1)`: `η_fine ≤ δ(r₀+hL) U A^(Cs+1)` and
`η_old ≤ δ(r₀) κ A^(Cs+1)` are both at most the spread unit times it. -/
noncomputable def fitFactor (A U κ : ℝ) (Cs : ℕ) : ℝ := (U + κ) * A ^ ((Cs : ℝ) + 1)

theorem one_le_scaleConst {Kd Cd : ℝ} (hKd : 0 ≤ Kd) (hCd : 0 ≤ Cd) : 1 ≤ scaleConst Kd Cd := by
  unfold scaleConst
  nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (10 * Cd), mul_nonneg hKd hCd]

theorem fitFactor_le {Kd Cd N U κ S : ℝ} {Cs : ℕ} (hN : 1 ≤ N) (hS : 0 ≤ S) (hKd : 0 ≤ Kd)
    (hCd : 0 ≤ Cd) (hU0 : 0 ≤ U) (hU : U ≤ N ^ (4 * S)) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ S) :
    fitFactor (sheetScale Kd Cd N U κ S) U κ Cs ≤
      2 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1) *
        N ^ ((4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S) := by
  have hN0 : 0 < N := by linarith
  set A := sheetScale Kd Cd N U κ S
  have hA := sheetScale_le hN hS hKd hCd hU0 hU hκ0 hκ
  have hA0 : 0 ≤ A := by have := (sheetScale_ge (S := S) hN0 hKd hCd hU0 hκ0).2.2.2.1; linarith
  have hCA : 0 ≤ scaleConst Kd Cd := (zero_le_one).trans (one_le_scaleConst hKd hCd)
  have hAC := mul_rpow_le_of_le hN0 hCA hA0 hA (by positivity : (0 : ℝ) ≤ (Cs : ℝ) + 1)
  have hS4 : N ^ S ≤ N ^ (4 * S) := rpow_mono_exp hN (by linarith)
  have hUκ : U + κ ≤ 2 * N ^ (4 * S) := by linarith
  have e : N ^ ((4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S) =
      N ^ (4 * S) * N ^ (((Cs : ℝ) + 1) * ((25 * Cd + 8) * S)) := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [e]
  unfold fitFactor
  have hK0 : 0 ≤ scaleConst Kd Cd ^ ((Cs : ℝ) + 1) := Real.rpow_nonneg hCA _
  calc (U + κ) * A ^ ((Cs : ℝ) + 1) ≤ (2 * N ^ (4 * S)) *
        (scaleConst Kd Cd ^ ((Cs : ℝ) + 1) * N ^ (((Cs : ℝ) + 1) * ((25 * Cd + 8) * S))) := by
        gcongr
    _ = _ := by ring

/-- The fit exponent is a quarter of the multiplier at most. -/
theorem fit_exponent_le {Cs : ℕ} {Cd Crem S : ℝ} (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem) (hS : 0 ≤ S) :
    (30 * Crem + 4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S ≤ expMult Cs Cd Crem * S / 4 := by
  unfold expMult
  have : 30 * Crem + 4 + ((Cs : ℝ) + 1) * (25 * Cd + 8) ≤
      (((Cs : ℝ) + 2) * (25 * Cd + 8) + 30 * Crem + 40) := by nlinarith
  nlinarith

/-- **The width condition** `3 · fitFactor ≤ R^εG` of the group step. -/
theorem group_width_numeric {Kd Cd Crem N U κ S r₀ h L gain εG : ℝ} {Cs : ℕ}
    (hN : 1 ≤ N) (hS : 0 ≤ S) (hKd : 0 ≤ Kd) (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem)
    (hU0 : 0 ≤ U) (hU : U ≤ N ^ (4 * S)) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ S)
    (hεG : 0 < εG) (hεG1 : εG ≤ 1) (hgain : 0 < gain) (hL : 0 < L) (hgh : gain ≤ h)
    (hbud : expMult Cs Cd Crem * S ≤ εG * gain * L / 8)
    (hNξ : (2 * (6 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1))) ^ (1 / (εG * gain * L / 2)) ≤ N) :
    3 * fitFactor (sheetScale Kd Cd N U κ S) U κ Cs ≤ cmpRatio N r₀ (h * L) ^ εG := by
  have hX := fitFactor_le (Cs := Cs) hN hS hKd hCd hU0 hU hκ0 hκ
  have hCA := one_le_scaleConst hKd hCd
  have hK1 : (1 : ℝ) ≤ 6 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1) := by
    have := Real.one_le_rpow hCA (by positivity : (0 : ℝ) ≤ (Cs : ℝ) + 1); linarith
  have hfe := fit_exponent_le (Cs := Cs) hCd hCrem hS
  have hgap : (4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S + εG * gain * L / 2 ≤ εG * (h * L) := by
    have h1 : (4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S ≤
        (30 * Crem + 4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S := by nlinarith
    have h2 : εG * gain * L ≤ εG * (h * L) := by
      have := mul_le_mul_of_nonneg_right hgh hL.le; nlinarith
    have h3 : (4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S ≤ εG * gain * L / 32 := by
      have := h1.trans hfe
      linarith
    have h4 : 0 ≤ εG * gain * L := by positivity
    linarith
  have hfin := le_cmpRatio_rpow (r₀ := r₀) hN hεG.le hεG1 (mul_nonneg (by linarith) hL.le) hK1
    (by positivity) hNξ hgap
  nlinarith

/-- The group projection floor. -/
noncomputable def groupFloor (N S : ℝ) : ℝ := N ^ (-(30 * S)) / 2 ^ 30

theorem groupFloor_pos {N : ℝ} (hN : 0 < N) (S : ℝ) : 0 < groupFloor N S := by
  unfold groupFloor; positivity

theorem groupFloor_rpow_neg {N : ℝ} (hN : 0 < N) (S C : ℝ) :
    groupFloor N S ^ (-C) = 2 ^ (30 * C) * N ^ (30 * C * S) := by
  unfold groupFloor
  rw [Real.div_rpow (Real.rpow_nonneg hN.le _) (by positivity), ← Real.rpow_mul hN.le]
  have h2 : ((2 : ℝ) ^ (30 : ℕ)) ^ (-C) = (2 : ℝ) ^ (-(30 * C)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; ring_nf
  rw [h2, Real.rpow_neg (by norm_num), div_inv_eq_mul, show -(30 * S) * -C = 30 * C * S by ring]
  ring

/-- **The Remez band condition** of the group step, with the group floor `θ_G`. -/
theorem group_band_numeric {Kd Cd Krem Crem N U κ S r₀ h L gain εG : ℝ} {Cs : ℕ}
    (hN : 1 ≤ N) (hS : 0 ≤ S) (hKd : 0 ≤ Kd) (hCd : 0 ≤ Cd) (hKrem : 1 ≤ Krem) (hCrem : 1 ≤ Crem)
    (hU0 : 0 ≤ U) (hU : U ≤ N ^ (4 * S)) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ S)
    (hεG : 0 < εG) (hεG1 : εG ≤ 1) (hgain : 0 < gain) (hL : 0 < L) (hgh : gain ≤ h)
    (hbud : expMult Cs Cd Crem * S ≤ εG * gain * L / 8)
    (hNξ : (2 * (2 * Krem * Crem * 2 ^ (30 * Crem) * scaleConst Kd Cd ^ ((Cs : ℝ) + 1))) ^
      (1 / (εG * gain * L / 2)) ≤ N) :
    Krem * (Crem * groupFloor N S ^ (-Crem) * fitFactor (sheetScale Kd Cd N U κ S) U κ Cs) ≤
      cmpRatio N r₀ (h * L) ^ εG := by
  have hN0 : 0 < N := by linarith
  have hX := fitFactor_le (Cs := Cs) hN hS hKd hCd hU0 hU hκ0 hκ
  have hCA := one_le_scaleConst hKd hCd
  have hCAp : 1 ≤ scaleConst Kd Cd ^ ((Cs : ℝ) + 1) := Real.one_le_rpow hCA (by positivity)
  have h2C : 1 ≤ (2 : ℝ) ^ (30 * Crem) := Real.one_le_rpow (by norm_num) (by linarith)
  set K₀ := 2 * Krem * Crem * 2 ^ (30 * Crem) * scaleConst Kd Cd ^ ((Cs : ℝ) + 1) with hK₀
  have hK1 : 1 ≤ K₀ := by
    have h1 : 1 ≤ Krem * Crem := by nlinarith
    have h2 : 1 ≤ Krem * Crem * 2 ^ (30 * Crem) := by nlinarith
    have h3 : 1 ≤ Krem * Crem * 2 ^ (30 * Crem) * scaleConst Kd Cd ^ ((Cs : ℝ) + 1) := by nlinarith
    rw [hK₀]; nlinarith
  have hfe := fit_exponent_le (Cs := Cs) (by linarith : (0:ℝ) ≤ Cd) (by linarith : (0:ℝ) ≤ Crem) hS
  have hgap : (30 * Crem + 4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S + εG * gain * L / 2 ≤
      εG * (h * L) := by
    have h2 : εG * gain * L ≤ εG * (h * L) := by
      have := mul_le_mul_of_nonneg_right hgh hL.le; nlinarith
    have h4 : 0 ≤ εG * gain * L := by positivity
    linarith
  have hfin := le_cmpRatio_rpow (r₀ := r₀) hN hεG.le hεG1 (mul_nonneg (by linarith) hL.le) hK1
    (by positivity) hNξ hgap
  rw [groupFloor_rpow_neg hN0]
  have e : N ^ ((30 * Crem + 4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S) =
      N ^ (30 * Crem * S) * N ^ ((4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S) := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [e] at hfin
  have hp0 : 0 ≤ N ^ (30 * Crem * S) := by positivity
  calc Krem * (Crem * (2 ^ (30 * Crem) * N ^ (30 * Crem * S)) *
        fitFactor (sheetScale Kd Cd N U κ S) U κ Cs)
      ≤ Krem * (Crem * (2 ^ (30 * Crem) * N ^ (30 * Crem * S)) *
        (2 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1) *
          N ^ ((4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S))) := by
        gcongr
    _ = K₀ * (N ^ (30 * Crem * S) * N ^ ((4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S)) := by
        rw [hK₀]; ring
    _ ≤ _ := hfin

/-- `R⁻¹ ≤ 2 N^(-hL)`. -/
theorem inv_cmpRatio_le {N r₀ hL : ℝ} (hN : 0 < N) :
    (cmpRatio N r₀ hL)⁻¹ ≤ 2 * N ^ (-hL) := by
  obtain ⟨hlo, -⟩ := cmpRatio_bounds hN r₀ hL
  have hp : 0 < N ^ hL / 2 := by positivity
  calc (cmpRatio N r₀ hL)⁻¹ ≤ (N ^ hL / 2)⁻¹ := inv_anti₀ hp hlo
    _ = 2 * N ^ (-hL) := by rw [Real.rpow_neg hN.le]; field_simp

/-- `R^(-ε) ≤ 2 N^(-ε hL)`. -/
theorem cmpRatio_rpow_neg_le {N r₀ hL ε : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hhL : 0 ≤ hL) : cmpRatio N r₀ hL ^ (-ε) ≤ 2 * N ^ (-(ε * hL)) := by
  have hN0 : 0 < N := by linarith
  have hR := cmpRatio_pos N r₀ hL
  have hlow := cmpRatio_rpow_lower (r₀ := r₀) hN hε hε1 hhL
  have hp : 0 < N ^ (ε * hL) / 2 := by positivity
  rw [Real.rpow_neg hR.le]
  calc (cmpRatio N r₀ hL ^ ε)⁻¹ ≤ (N ^ (ε * hL) / 2)⁻¹ := inv_anti₀ hp hlow
    _ = 2 * N ^ (-(ε * hL)) := by rw [Real.rpow_neg hN0.le]; field_simp

/-- **The root-test target** `340 (X/R + Jsum R^(-εG)/lower) ≤ N^(-θ h L)`. -/
theorem group_root_numeric {Kd Cd Crem N U κ S r₀ h L gain εG θo Jsum lower : ℝ} {Cs : ℕ}
    (hN : 1 ≤ N) (hS : 0 ≤ S) (hKd : 0 ≤ Kd) (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem)
    (hU0 : 0 ≤ U) (hU : U ≤ N ^ (4 * S)) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ S)
    (hεG : 0 < εG) (hεG2 : εG ≤ 1 / 2) (hθ0 : 0 ≤ θo) (hθ : θo ≤ εG / 4)
    (hgain : 0 < gain) (hL : 0 < L) (hgh : gain ≤ h) (hJ : 0 ≤ Jsum) (hlower : 0 < lower)
    (hbud : expMult Cs Cd Crem * S ≤ εG * gain * L / 8)
    (hN1 : (2720 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1)) ^ (1 / (gain * L / 2)) ≤ N)
    (hN2 : (1360 * Jsum / lower + 1) ^ (1 / (εG * gain * L / 2)) ≤ N) :
    340 * (fitFactor (sheetScale Kd Cd N U κ S) U κ Cs / cmpRatio N r₀ (h * L) +
      Jsum * cmpRatio N r₀ (h * L) ^ (-εG) / lower) ≤ N ^ (-(θo * (h * L))) := by
  have hN0 : 0 < N := by linarith
  have hhL : 0 ≤ h * L := mul_nonneg (by linarith) hL.le
  have hgL : gain * L ≤ h * L := mul_le_mul_of_nonneg_right hgh hL.le
  have hX := fitFactor_le (Cs := Cs) hN hS hKd hCd hU0 hU hκ0 hκ
  have hCA := one_le_scaleConst hKd hCd
  have hCAp : 1 ≤ scaleConst Kd Cd ^ ((Cs : ℝ) + 1) := Real.one_le_rpow hCA (by positivity)
  have hfe := fit_exponent_le (Cs := Cs) hCd hCrem hS
  set a := (4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S with ha
  have ha0 : a ≤ εG * gain * L / 32 := by
    have h1 : a ≤ (30 * Crem + 4 + ((Cs : ℝ) + 1) * (25 * Cd + 8)) * S := by
      rw [ha]; nlinarith
    linarith
  have hεgL : εG * gain * L ≤ gain * L / 2 := by nlinarith [mul_pos hgain hL]
  -- first term
  have hT1 : 340 * (fitFactor (sheetScale Kd Cd N U κ S) U κ Cs / cmpRatio N r₀ (h * L)) ≤
      N ^ (-(θo * (h * L))) / 2 := by
    have hinv := inv_cmpRatio_le (r₀ := r₀) (hL := h * L) hN0
    have hgap : (a - h * L) + gain * L / 2 ≤ -(θo * (h * L)) := by
      have : θo * (h * L) ≤ h * L / 8 := by nlinarith
      linarith
    have habs := rpow_absorb hN (by linarith : (1 : ℝ) ≤ 2720 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1))
      (by positivity : (0 : ℝ) < gain * L / 2) hN1 hgap
    have e : N ^ (a - h * L) = N ^ a * N ^ (-(h * L)) := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [e] at habs
    have hR0 : 0 ≤ (cmpRatio N r₀ (h * L))⁻¹ := inv_nonneg.mpr (cmpRatio_pos _ _ _).le
    calc 340 * (fitFactor (sheetScale Kd Cd N U κ S) U κ Cs / cmpRatio N r₀ (h * L))
        = 340 * (fitFactor (sheetScale Kd Cd N U κ S) U κ Cs * (cmpRatio N r₀ (h * L))⁻¹) := by
          rw [div_eq_mul_inv]
      _ ≤ 340 * ((2 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1) * N ^ a) * (2 * N ^ (-(h * L)))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hX hinv hR0 (by positivity)
      _ = (2720 * scaleConst Kd Cd ^ ((Cs : ℝ) + 1) * (N ^ a * N ^ (-(h * L)))) / 2 := by ring
      _ ≤ N ^ (-(θo * (h * L))) / 2 := by gcongr
  -- second term
  have hT2 : 340 * (Jsum * cmpRatio N r₀ (h * L) ^ (-εG) / lower) ≤ N ^ (-(θo * (h * L))) / 2 := by
    have hneg := cmpRatio_rpow_neg_le (r₀ := r₀) hN hεG.le (by linarith) hhL
    have hgap : -(εG * (h * L)) + εG * gain * L / 2 ≤ -(θo * (h * L)) := by
      have : θo * (h * L) ≤ εG * (h * L) / 4 := by nlinarith
      have : εG * gain * L ≤ εG * (h * L) := by nlinarith
      have : 0 ≤ εG * (h * L) := mul_nonneg hεG.le hhL
      linarith
    have hK : (1 : ℝ) ≤ 1360 * Jsum / lower + 1 := by
      have : 0 ≤ 1360 * Jsum / lower := by positivity
      linarith
    have habs := rpow_absorb hN hK (by positivity : (0 : ℝ) < εG * gain * L / 2) hN2 hgap
    have hJl : 0 ≤ Jsum / lower := by positivity
    calc 340 * (Jsum * cmpRatio N r₀ (h * L) ^ (-εG) / lower)
        = 340 * (Jsum / lower) * cmpRatio N r₀ (h * L) ^ (-εG) := by ring
      _ ≤ 340 * (Jsum / lower) * (2 * N ^ (-(εG * (h * L)))) := by gcongr
      _ = (1360 * Jsum / lower) * N ^ (-(εG * (h * L))) / 2 := by ring
      _ ≤ (1360 * Jsum / lower + 1) * N ^ (-(εG * (h * L))) / 2 := by
          gcongr; linarith
      _ ≤ N ^ (-(θo * (h * L))) / 2 := by gcongr
  have hsplit : 340 * (fitFactor (sheetScale Kd Cd N U κ S) U κ Cs / cmpRatio N r₀ (h * L) +
      Jsum * cmpRatio N r₀ (h * L) ^ (-εG) / lower) =
      340 * (fitFactor (sheetScale Kd Cd N U κ S) U κ Cs / cmpRatio N r₀ (h * L)) +
      340 * (Jsum * cmpRatio N r₀ (h * L) ^ (-εG) / lower) := by ring
  rw [hsplit]
  linarith

theorem expMult_ge {Cs : ℕ} {Cd Crem : ℝ} (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem) :
    160 ≤ expMult Cs Cd Crem := by
  unfold expMult; nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (Cs : ℝ) + 2)
    (by linarith : (0:ℝ) ≤ 25 * Cd + 8)]

/-- The greedy slack is tiny against the matching budget. -/
theorem slack_small {Cs : ℕ} {Cd Crem S εG gain L : ℝ} (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem)
    (hS : 0 ≤ S) (hbud : expMult Cs Cd Crem * S ≤ εG * gain * L / 8) :
    S ≤ εG * gain * L / 1280 := by
  have h := expMult_ge (Cs := Cs) hCd hCrem
  nlinarith

/-- **The count condition** `n ≤ R^(d₁ + εG)` for `n ≤ N^((d₁ h + 4ρ gain) L + 4ε)`. -/
theorem group_count_numeric {Cs : ℕ} {Cd Crem N ρ gain L ε σ τ h d₁ εG n r₀ : ℝ}
    (hN : 1 ≤ N) (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem) (hρ : 0 ≤ ρ) (hgain : 0 < gain) (hL : 0 < L)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hgh : gain ≤ h) (hd₁ : 0 ≤ d₁)
    (hεG : 0 < εG) (hdε : d₁ + εG ≤ 1)
    (hbud : expMult Cs Cd Crem * slackTot ρ gain L ε σ τ ≤ εG * gain * L / 8)
    (hN2 : (2 : ℝ) ^ (1 / (εG * gain * L / 2)) ≤ N)
    (hn : n ≤ N ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε)) :
    n ≤ cmpRatio N r₀ (h * L) ^ (d₁ + εG) := by
  have hS0 : 0 ≤ slackTot ρ gain L ε σ τ := by unfold slackTot; positivity
  have hsm := slack_small hCd hCrem hS0 hbud
  have hgs : greedySlack ρ gain L ε ≤ 4 * slackTot ρ gain L ε σ τ :=
    greedySlack_le (by positivity) hε hσ hτ
  have hhL : 0 ≤ h * L := mul_nonneg (by linarith) hL.le
  refine group_count hN hεG.le hd₁ hdε hhL (by positivity) hN2 hn ?_
  have h1 : εG * gain * L ≤ εG * (h * L) := by
    have := mul_le_mul_of_nonneg_right hgh hL.le; nlinarith
  unfold greedySlack at hgs
  nlinarith

/-- **The radius condition** of the group step. -/
theorem group_radius_numeric {N r₀ h L gain radius : ℝ} (hN : 1 ≤ N) (hgain : 0 < gain)
    (hL : 0 < L) (hgh : gain ≤ h) (hrad : 0 ≤ radius)
    (hN2 : (2 * radius + 1) ^ (1 / (gain * L)) ≤ N) : radius ≤ cmpRatio N r₀ (h * L) := by
  have hN0 : 0 < N := by linarith
  obtain ⟨hlo, -⟩ := cmpRatio_bounds hN0 r₀ (h * L)
  have h1 := rpow_absorb (a := 0) hN (by linarith : (1 : ℝ) ≤ 2 * radius + 1)
    (mul_pos hgain hL) hN2 (by simpa using mul_le_mul_of_nonneg_right hgh hL.le)
  rw [Real.rpow_zero, mul_one] at h1
  linarith

/-- **Error budgets.** The matching tail `R^(-εG)`, any tail `K₀ N^b R^(-2εG)` with
`b ≤ εG gain L / 4`, the light-entry tail `4 N^(-ε-τ)` are each at most `N^(-ε)/64`; and
`N^(-β) ≤ N^(-ε)/4` for `ε ≤ β/2`. -/
theorem error_budget_match {Cs : ℕ} {Cd Crem N ρ gain L ε σ τ h εG r₀ : ℝ}
    (hN : 1 ≤ N) (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem) (hρ : 0 ≤ ρ) (hgain : 0 < gain) (hL : 0 < L)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hgh : gain ≤ h) (hεG : 0 < εG) (hεG2 : εG ≤ 1 / 2)
    (hbud : expMult Cs Cd Crem * slackTot ρ gain L ε σ τ ≤ εG * gain * L / 8)
    (hN2 : (128 : ℝ) ^ (1 / (εG * gain * L / 2)) ≤ N) :
    cmpRatio N r₀ (h * L) ^ (-εG) ≤ N ^ (-ε) / 64 := by
  have hS0 : 0 ≤ slackTot ρ gain L ε σ τ := by unfold slackTot; positivity
  have hsm := slack_small hCd hCrem hS0 hbud
  have hεS : ε ≤ slackTot ρ gain L ε σ τ := by unfold slackTot; nlinarith
  have hhL : 0 ≤ h * L := mul_nonneg (by linarith) hL.le
  have hneg := cmpRatio_rpow_neg_le (r₀ := r₀) hN hεG.le (by linarith) hhL
  have h1 : εG * gain * L ≤ εG * (h * L) := by
    have := mul_le_mul_of_nonneg_right hgh hL.le; nlinarith
  have habs := rpow_absorb hN (by norm_num : (1 : ℝ) ≤ 128) (by positivity) hN2
    (show -(εG * (h * L)) + εG * gain * L / 2 ≤ -ε by nlinarith)
  linarith

theorem error_budget_pair {Cs : ℕ} {Cd Crem N ρ gain L ε σ τ h εG r₀ K₀ b : ℝ}
    (hN : 1 ≤ N) (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem) (hρ : 0 ≤ ρ) (hgain : 0 < gain) (hL : 0 < L)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hgh : gain ≤ h) (hεG : 0 < εG) (hεG2 : εG ≤ 1 / 2)
    (hK₀ : 0 ≤ K₀) (hb : b ≤ εG * gain * L / 4)
    (hbud : expMult Cs Cd Crem * slackTot ρ gain L ε σ τ ≤ εG * gain * L / 8)
    (hN2 : (256 * K₀ + 1) ^ (1 / (εG * gain * L / 2)) ≤ N) :
    K₀ * N ^ b * cmpRatio N r₀ (h * L) ^ (-(2 * εG)) ≤ N ^ (-ε) / 64 := by
  have hN0 : 0 < N := by linarith
  have hS0 : 0 ≤ slackTot ρ gain L ε σ τ := by unfold slackTot; positivity
  have hsm := slack_small hCd hCrem hS0 hbud
  have hεS : ε ≤ slackTot ρ gain L ε σ τ := by unfold slackTot; nlinarith
  have hhL : 0 ≤ h * L := mul_nonneg (by linarith) hL.le
  have hneg := cmpRatio_rpow_neg_le (r₀ := r₀) hN (by linarith : (0:ℝ) ≤ 2 * εG)
    (by linarith) hhL
  have h1 : εG * gain * L ≤ εG * (h * L) := by
    have := mul_le_mul_of_nonneg_right hgh hL.le; nlinarith
  have habs := rpow_absorb hN (by linarith : (1 : ℝ) ≤ 256 * K₀ + 1) (by positivity) hN2
    (show b - 2 * εG * (h * L) + εG * gain * L / 2 ≤ -ε by nlinarith)
  have e : N ^ (b - 2 * εG * (h * L)) = N ^ b * N ^ (-(2 * εG * (h * L))) := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [e] at habs
  have hNb : 0 ≤ N ^ b := by positivity
  calc K₀ * N ^ b * cmpRatio N r₀ (h * L) ^ (-(2 * εG))
      ≤ K₀ * N ^ b * (2 * N ^ (-(2 * εG * (h * L)))) := by
        gcongr
    _ ≤ (256 * K₀ + 1) * (N ^ b * N ^ (-(2 * εG * (h * L)))) / 64 := by
        have : 0 ≤ N ^ b * N ^ (-(2 * εG * (h * L))) := by positivity
        nlinarith
    _ ≤ N ^ (-ε) / 64 := by gcongr

theorem error_budget_light {N ε τ : ℝ} (hN : 1 ≤ N) (hτ : 0 < τ)
    (hN2 : (256 : ℝ) ^ (1 / τ) ≤ N) : 4 * N ^ (-ε - τ) ≤ N ^ (-ε) / 64 := by
  have h := rpow_absorb hN (by norm_num : (1 : ℝ) ≤ 256) hτ hN2 (show (-ε - τ) + τ ≤ -ε by linarith)
  linarith

theorem error_budget_final {N ε β : ℝ} (hN : 1 ≤ N) (hβ : 0 < β) (hεβ : ε ≤ β / 2)
    (hN2 : (4 : ℝ) ^ (1 / (β / 2)) ≤ N) : N ^ (-β) ≤ N ^ (-ε) / 4 := by
  have h := rpow_absorb hN (by norm_num : (1 : ℝ) ≤ 4) (by positivity) hN2
    (show -β + β / 2 ≤ -ε by linarith)
  linarith

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
