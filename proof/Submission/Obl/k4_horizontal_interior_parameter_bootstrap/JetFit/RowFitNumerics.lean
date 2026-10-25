import Mathlib

/-!
# Numerics of the row fit

The smallness conditions of `block_fit` at the planar scale `p = H^(1/4)` and the constant
`Ks = Cs N^(17η)` (`Cs = 224 · 10^5`, the constant `224 (10K³)^5 / τ²` at `K = N^η`,
`τ = N^(-η)`), for block lengths `N^(-c'') ≤ H ≤ N^(-c')`, follow from finitely many
inequalities between powers of `N` (`RowFitConds`), which hold for all large `N` once `η` is
small (`rowFitConds_eventually`).
-/

open Filter

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

/-- The constant `224 · 10^5`. -/
def Cs : ℝ := 22400000

theorem Cs_pos : (0 : ℝ) < Cs := by norm_num [Cs]

theorem one_le_Cs : (1 : ℝ) ≤ Cs := by norm_num [Cs]

/-- Powers beat constants. -/
theorem eventually_mul_rpow_le (C : ℝ) {x y : ℝ} (hxy : x < y) :
    ∀ᶠ N : ℝ in atTop, C * N ^ x ≤ N ^ y := by
  have h := tendsto_rpow_atTop (sub_pos.2 hxy)
  filter_upwards [h.eventually_ge_atTop C, eventually_gt_atTop 0] with N hN hN0
  calc C * N ^ x ≤ N ^ (y - x) * N ^ x :=
        mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = N ^ y := by rw [← Real.rpow_add hN0]; ring_nf

/-- The inequalities between powers of `N` used by the row fit. -/
structure RowFitConds (N η ηb δ₀ ε d c' c'' ε₁ : ℝ) : Prop where
  ha : N ^ (-(c' / 4)) ≤ 8 * δ₀
  hb : 65 * Cs * N ^ (17 * η) ≤ N ^ (c' / 4 * ηb)
  hc : (288 * Cs ^ 3 + 1) * N ^ (51 * η) ≤ N ^ (c' / 4 * (ηb * (1 - ε - d)))
  hd : 27 * 179712 * 512 * Cs ^ 19 * N ^ (323 * η) ≤ N ^ (c' / 4 * ηb)
  he : 3250 * Cs ^ 2 * N ^ (34 * η) ≤ N ^ (c' / 4 * (1 - ε))
  hf : 5 * 325 * 36864 * Cs ^ 18 * N ^ (306 * η) ≤ N ^ (ε₁ - c'' / 4 * ε)
  hg : (12 * Cs + 13) * N ^ (17 * η) ≤ N ^ ε₁

/-- The conditions hold for all large `N` when `η` is small. -/
theorem rowFitConds_eventually {ηb δ₀ ε d c' c'' ε₁ : ℝ} (hηb : 0 < ηb) (hδ₀ : 0 < δ₀)
    (hd : 0 ≤ d) (hd1 : d < 1) (hc' : 0 < c') (hc'c'' : c' ≤ c'') (hε₁ : 0 < ε₁)
    (hε : 0 < ε) (hε2 : ε ≤ (1 - d) / 2) (hεc : ε ≤ ε₁ / (8 * c'')) :
    ∀ᶠ N : ℝ in atTop, RowFitConds N (min (c' * ηb * (1 - d) / 2000) (min (c' / 400) (ε₁ / 400)))
      ηb δ₀ ε d c' c'' ε₁ := by
  set η := min (c' * ηb * (1 - d) / 2000) (min (c' / 400) (ε₁ / 400)) with hη_def
  have hX : 0 < c' * ηb * (1 - d) := by
    have : 0 < 1 - d := by linarith
    positivity
  have hη1 : η ≤ c' * ηb * (1 - d) / 2000 := min_le_left _ _
  have hη2 : η ≤ c' / 400 := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ ε₁ / 400 := (min_le_right _ _).trans (min_le_right _ _)
  have hcηb : c' * ηb * (1 - d) ≤ c' * ηb := by
    have : 0 ≤ c' * ηb := by positivity
    nlinarith
  have hc''pos : 0 < c'' := hc'.trans_le hc'c''
  -- (a)
  have ha : ∀ᶠ N : ℝ in atTop, N ^ (-(c' / 4)) ≤ 8 * δ₀ := by
    have h := tendsto_rpow_neg_atTop (show 0 < c' / 4 by positivity)
    have := (tendsto_order.1 h).2 (8 * δ₀) (by positivity)
    filter_upwards [this] with N hN using hN.le
  have hb := eventually_mul_rpow_le (65 * Cs) (x := 17 * η) (y := c' / 4 * ηb) (by
    have : c' * ηb * (1 - d) / 2000 ≤ c' * ηb / 2000 := by linarith
    have : 0 < c' * ηb := by positivity
    linarith)
  have hc := eventually_mul_rpow_le (288 * Cs ^ 3 + 1) (x := 51 * η)
    (y := c' / 4 * (ηb * (1 - ε - d))) (by
    have h1 : c' / 4 * (ηb * (1 - ε - d)) - c' * ηb * (1 - d) / 8 =
        c' * ηb / 4 * ((1 - d) / 2 - ε) := by ring
    have h2 : 0 ≤ c' * ηb / 4 * ((1 - d) / 2 - ε) := by
      have : 0 ≤ (1 - d) / 2 - ε := by linarith
      positivity
    linarith)
  have hd' := eventually_mul_rpow_le (27 * 179712 * 512 * Cs ^ 19) (x := 323 * η)
    (y := c' / 4 * ηb) (by
    have : 0 < c' * ηb := by positivity
    linarith)
  have he := eventually_mul_rpow_le (3250 * Cs ^ 2) (x := 34 * η) (y := c' / 4 * (1 - ε)) (by
    have h1 : c' / 4 * (1 - ε) - c' / 8 = c' / 4 * (1 / 2 - ε) := by ring
    have h2 : 0 ≤ c' / 4 * (1 / 2 - ε) := by
      have : ε ≤ 1 / 2 := by linarith
      have : 0 ≤ 1 / 2 - ε := by linarith
      positivity
    linarith)
  have hf := eventually_mul_rpow_le (5 * 325 * 36864 * Cs ^ 18) (x := 306 * η)
    (y := ε₁ - c'' / 4 * ε) (by
    have h1 : c'' * ε ≤ ε₁ / 8 := by
      rw [le_div_iff₀ (by positivity)] at hεc
      nlinarith
    linarith)
  have hg := eventually_mul_rpow_le (12 * Cs + 13) (x := 17 * η) (y := ε₁) (by linarith)
  filter_upwards [ha, hb, hc, hd', he, hf, hg] with N h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- `δ^(-e) ≥ N^(c'/4 · e)` when `δ ≤ N^(-(c'/4))`. -/
theorem rpow_neg_ge {N δ c' e : ℝ} (hN : 0 < N) (hδ : 0 < δ) (hδP : δ ≤ N ^ (-(c' / 4)))
    (he : 0 ≤ e) : N ^ (c' / 4 * e) ≤ δ ^ (-e) := by
  have h1 : (N ^ (-(c' / 4))) ^ (-e) ≤ δ ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos hδ hδP (by linarith)
  have h2 : (N ^ (-(c' / 4))) ^ (-e) = N ^ (c' / 4 * e) := by
    rw [← Real.rpow_mul hN.le]; ring_nf
  linarith

theorem rpow_three (x : ℝ) : x ^ (3 : ℝ) = x ^ 3 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem rpow_mul_nat {N : ℝ} (hN : 0 < N) (a : ℝ) (n : ℕ) : (N ^ a) ^ n = N ^ (n * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; ring_nf

/-- The block-fit conditions at `p = H^(1/4)`, `Ks = Cs N^(17η)`. -/
theorem block_numerics {N η ηb δ₀ ε d c' c'' ε₁ H : ℝ} (hN : 1 ≤ N) (hη : 0 < η)
    (hηb : 0 < ηb) (hc' : 0 < c') (hd : 0 ≤ d) (hεd : ε + d < 1)
    (hH1 : N ^ (-c'') ≤ H) (hH2 : H ≤ N ^ (-c'))
    (hC : RowFitConds N η ηb δ₀ ε d c' c'' ε₁) :
    0 < H ^ (1 / 4 : ℝ) ∧ H ^ (1 / 4 : ℝ) ≤ 1 ∧ 1 ≤ Cs * N ^ (17 * η) ∧
    H ^ (1 / 4 : ℝ) / (8 * (Cs * N ^ (17 * η))) ≤ δ₀ ∧
    5 * (8 * (Cs * N ^ (17 * η)) + 5) ≤
      (H ^ (1 / 4 : ℝ) / (8 * (Cs * N ^ (17 * η)))) ^ (-ηb) ∧
    3 * (4 * (Cs * N ^ (17 * η))) ^ 2 * (4 * (Cs * N ^ (17 * η)) + 2) <
      (H ^ (1 / 4 : ℝ) / (8 * (Cs * N ^ (17 * η)))) ^ (-ηb * (1 - ε - d)) ∧
    27 * 179712 * (Cs * N ^ (17 * η)) ^ 16 * (H ^ (1 / 4 : ℝ)) ^ 3 *
      (H ^ (1 / 4 : ℝ) / (8 * (Cs * N ^ (17 * η)))) ^ (ηb - 3) ≤ 1 ∧
    10 * ((4 * (2 * (Cs * N ^ (17 * η))) + 5) * (8 * (2 * (Cs * N ^ (17 * η))) + 9)) *
      (H ^ (1 / 4 : ℝ) / (8 * (Cs * N ^ (17 * η)))) ≤
      (H ^ (1 / 4 : ℝ) / (8 * (Cs * N ^ (17 * η)))) ^ ε := by
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hH1
  set p := H ^ (1 / 4 : ℝ) with hp_def
  set Q := N ^ (17 * η) with hQ_def
  set Ks := Cs * Q with hKs_def
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hN (by positivity)
  have hKs1 : 1 ≤ Ks := by have := one_le_Cs; nlinarith
  have hKs0 : 0 < Ks := by linarith
  have hp0 : 0 < p := Real.rpow_pos_of_pos hH0 _
  have hPp : p ≤ N ^ (-(c' / 4)) := by
    have := Real.rpow_le_rpow hH0.le hH2 (by norm_num : (0:ℝ) ≤ 1 / 4)
    rw [← Real.rpow_mul hN0.le] at this
    calc p ≤ N ^ (-c' * (1 / 4)) := this
      _ = N ^ (-(c' / 4)) := by ring_nf
  have hP1 : N ^ (-(c' / 4)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hp1 : p ≤ 1 := hPp.trans hP1
  set δ := p / (8 * Ks) with hδ_def
  have hδ0 : 0 < δ := by positivity
  have hδp : δ ≤ p := div_le_self hp0.le (by linarith)
  have hδP : δ ≤ N ^ (-(c' / 4)) := hδp.trans hPp
  refine ⟨hp0, hp1, hKs1, ?_, ?_, ?_, ?_, ?_⟩
  · have : δ ≤ p / 8 := div_le_div_of_nonneg_left hp0.le (by norm_num) (by linarith)
    have := hC.ha
    linarith
  · have h1 := rpow_neg_ge hN0 hδ0 hδP hηb.le
    have h2 := hC.hb
    calc 5 * (8 * Ks + 5) ≤ 65 * Ks := by linarith
      _ = 65 * Cs * N ^ (17 * η) := by rw [hKs_def]; ring
      _ ≤ N ^ (c' / 4 * ηb) := h2
      _ ≤ δ ^ (-ηb) := h1
  · have he : 0 ≤ ηb * (1 - ε - d) := by
      have : 0 < 1 - ε - d := by linarith
      positivity
    have h1 := rpow_neg_ge hN0 hδ0 hδP he
    have h3 : N ^ (51 * η) = Q ^ 3 := by
      rw [hQ_def, rpow_mul_nat hN0]; push_cast; ring_nf
    have hk : 3 * (4 * Ks) ^ 2 * (4 * Ks + 2) ≤ 288 * Ks ^ 3 := by nlinarith
    have hQ3 : 0 < Q ^ 3 := by positivity
    have hlt : 3 * (4 * Ks) ^ 2 * (4 * Ks + 2) < (288 * Cs ^ 3 + 1) * N ^ (51 * η) := by
      rw [h3]
      calc 3 * (4 * Ks) ^ 2 * (4 * Ks + 2) ≤ 288 * Ks ^ 3 := hk
        _ = 288 * Cs ^ 3 * Q ^ 3 := by rw [hKs_def]; ring
        _ < (288 * Cs ^ 3 + 1) * Q ^ 3 := by nlinarith
    calc 3 * (4 * Ks) ^ 2 * (4 * Ks + 2) < (288 * Cs ^ 3 + 1) * N ^ (51 * η) := hlt
      _ ≤ N ^ (c' / 4 * (ηb * (1 - ε - d))) := hC.hc
      _ ≤ δ ^ (-(ηb * (1 - ε - d))) := h1
      _ = δ ^ (-ηb * (1 - ε - d)) := by ring_nf
  · have hsplit : δ ^ (ηb - 3) = δ ^ ηb / δ ^ 3 := by
      rw [Real.rpow_sub hδ0, rpow_three]
    have hδ3 : δ ^ 3 = p ^ 3 / (8 * Ks) ^ 3 := by rw [hδ_def, div_pow]
    have hp3 : 0 < p ^ 3 := by positivity
    have hKs3 : 0 < (8 * Ks) ^ 3 := by positivity
    have hmain : p ^ 3 * δ ^ (ηb - 3) = (8 * Ks) ^ 3 * δ ^ ηb := by
      rw [hsplit, hδ3]; field_simp
    have hδη : δ ^ ηb ≤ N ^ (-(c' / 4 * ηb)) := by
      have := Real.rpow_le_rpow hδ0.le hδP hηb.le
      rw [← Real.rpow_mul hN0.le] at this
      calc δ ^ ηb ≤ N ^ (-(c' / 4) * ηb) := this
        _ = N ^ (-(c' / 4 * ηb)) := by ring_nf
    have hQ19 : Q ^ 19 = N ^ (323 * η) := by
      rw [hQ_def, rpow_mul_nat hN0]; push_cast; ring_nf
    have hd := hC.hd
    have hprod : N ^ (c' / 4 * ηb) * N ^ (-(c' / 4 * ηb)) = 1 := by
      rw [← Real.rpow_add hN0]; simp
    have hnn : 0 ≤ N ^ (-(c' / 4 * ηb)) := Real.rpow_nonneg hN0.le _
    calc 27 * 179712 * Ks ^ 16 * p ^ 3 * δ ^ (ηb - 3)
        = 27 * 179712 * Ks ^ 16 * (p ^ 3 * δ ^ (ηb - 3)) := by ring
      _ = 27 * 179712 * 512 * Cs ^ 19 * Q ^ 19 * δ ^ ηb := by rw [hmain, hKs_def]; ring
      _ ≤ 27 * 179712 * 512 * Cs ^ 19 * Q ^ 19 * N ^ (-(c' / 4 * ηb)) := by
          apply mul_le_mul_of_nonneg_left hδη; have := Cs_pos; positivity
      _ = (27 * 179712 * 512 * Cs ^ 19 * N ^ (323 * η)) * N ^ (-(c' / 4 * ηb)) := by
          rw [hQ19]
      _ ≤ N ^ (c' / 4 * ηb) * N ^ (-(c' / 4 * ηb)) := mul_le_mul_of_nonneg_right hd hnn
      _ = 1 := hprod
  · have hC0 : (4 * (2 * Ks) + 5) * (8 * (2 * Ks) + 9) ≤ 325 * Ks ^ 2 := by nlinarith
    have he : 0 ≤ 1 - ε := by linarith
    have h1 := rpow_neg_ge hN0 hδ0 hδP he
    have h2 := hC.he
    have hQ2 : Q ^ 2 = N ^ (34 * η) := by
      rw [hQ_def, rpow_mul_nat hN0]; push_cast; ring_nf
    have h3 : 3250 * Ks ^ 2 ≤ δ ^ (-(1 - ε)) := by
      calc 3250 * Ks ^ 2 = 3250 * Cs ^ 2 * Q ^ 2 := by rw [hKs_def]; ring
        _ = 3250 * Cs ^ 2 * N ^ (34 * η) := by rw [hQ2]
        _ ≤ N ^ (c' / 4 * (1 - ε)) := h2
        _ ≤ δ ^ (-(1 - ε)) := h1
    have h4 : δ ^ (-(1 - ε)) * δ = δ ^ ε := by
      rw [← Real.rpow_add_one hδ0.ne']; congr 1; ring
    calc 10 * ((4 * (2 * Ks) + 5) * (8 * (2 * Ks) + 9)) * δ ≤ 10 * (325 * Ks ^ 2) * δ := by
          apply mul_le_mul_of_nonneg_right _ hδ0.le; linarith
      _ = 3250 * Ks ^ 2 * δ := by ring
      _ ≤ δ ^ (-(1 - ε)) * δ := mul_le_mul_of_nonneg_right h3 hδ0.le
      _ = δ ^ ε := h4

/-- The output conversions of the row fit. -/
theorem fit_outputs {N η ε c'' ε₁ H ζ : ℝ} (hN : 1 ≤ N) (hη : 0 < η) (hε : 0 < ε)
    (hH0 : 0 < H) (hH1 : N ^ (-c'') ≤ H) (hHle1 : H ≤ 1) (hζ : 0 < ζ) (hζH : ζ ≤ H ^ 8)
    (hf : 5 * 325 * 36864 * Cs ^ 18 * N ^ (306 * η) ≤ N ^ (ε₁ - c'' / 4 * ε))
    (hg : (12 * Cs + 13) * N ^ (17 * η) ≤ N ^ ε₁) :
    H ≤ H ^ (1 / 4 : ℝ) ∧ ζ ≤ H * H ^ (1 / 4 : ℝ) ∧
    224 * (10 * (N ^ η) ^ 3) ^ 5 / (N ^ (-η)) ^ 2 ≤ Cs * N ^ (17 * η) ∧
    6 * (Cs * N ^ (17 * η)) + 1 ≤ N ^ ε₁ ∧
    H * ((12 * (Cs * N ^ (17 * η)) + 2) * H ^ (1 / 4 : ℝ)) + 10 * (N ^ η) ^ 3 * ζ ≤
      N ^ ε₁ * H ^ (5 / 4 : ℝ) ∧
    N ^ (-ε₁) * H ≤ H * ((H ^ (1 / 4 : ℝ)) ^ ε /
      (5 * ((4 * (2 * (Cs * N ^ (17 * η))) + 5) * (8 * (2 * (Cs * N ^ (17 * η))) + 9)) *
        (36864 * (Cs * N ^ (17 * η)) ^ 16))) := by
  have hN0 : 0 < N := by linarith
  set Q := N ^ (17 * η) with hQ_def
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hN (by positivity)
  set p := H ^ (1 / 4 : ℝ) with hp_def
  have hp0 : 0 < p := Real.rpow_pos_of_pos hH0 _
  have hHp : H ≤ p := by
    have := Real.rpow_le_rpow_of_exponent_ge hH0 hHle1 (show (1 / 4 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have h54 : H ^ (5 / 4 : ℝ) = H * p := by
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hH0, Real.rpow_one]
  have hH8 : H ^ 8 ≤ H ^ (5 / 4 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hH0 hHle1 (by norm_num)
  set K := N ^ η with hK_def
  have hK0 : 0 < K := Real.rpow_pos_of_pos hN0 _
  have hK3 : K ^ 3 ≤ Q := by
    rw [hK_def, rpow_mul_nat hN0, hQ_def]
    exact Real.rpow_le_rpow_of_exponent_le hN (by push_cast; linarith)
  have hKs1 : 1 ≤ Cs * Q := by have := one_le_Cs; nlinarith
  refine ⟨hHp, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : H ^ 8 ≤ H ^ 2 := pow_le_pow_of_le_one hH0.le hHle1 (by norm_num)
    have h2 : H ^ 2 ≤ H * p := by rw [sq]; exact mul_le_mul_of_nonneg_left hHp hH0.le
    linarith
  · apply le_of_eq
    have hK17 : K ^ 17 = Q := by rw [hK_def, rpow_mul_nat hN0, hQ_def]; push_cast; ring_nf
    rw [Real.rpow_neg hN0.le, ← hK_def, ← hK17, Cs]
    field_simp
    ring
  · have := one_le_Cs
    have := Cs_pos
    nlinarith
  · have hζ' : ζ ≤ H ^ (5 / 4 : ℝ) := hζH.trans hH8
    have h1 : H * ((12 * (Cs * Q) + 2) * p) = (12 * (Cs * Q) + 2) * H ^ (5 / 4 : ℝ) := by
      rw [h54]; ring
    have h2 : 10 * K ^ 3 * ζ ≤ 10 * Q * H ^ (5 / 4 : ℝ) := by
      apply mul_le_mul (by linarith) hζ' hζ.le (by positivity)
    have h3 : 12 * (Cs * Q) + 2 + 10 * Q ≤ N ^ ε₁ := by
      have := Cs_pos
      nlinarith
    have h5 : 0 ≤ H ^ (5 / 4 : ℝ) := Real.rpow_nonneg hH0.le _
    calc H * ((12 * (Cs * Q) + 2) * p) + 10 * K ^ 3 * ζ
        ≤ (12 * (Cs * Q) + 2) * H ^ (5 / 4 : ℝ) + 10 * Q * H ^ (5 / 4 : ℝ) := by
          rw [h1]; linarith
      _ = (12 * (Cs * Q) + 2 + 10 * Q) * H ^ (5 / 4 : ℝ) := by ring
      _ ≤ N ^ ε₁ * H ^ (5 / 4 : ℝ) := mul_le_mul_of_nonneg_right h3 h5
  · have hpge : N ^ (-(c'' / 4)) ≤ p := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hH1 (by norm_num : (0:ℝ) ≤ 1 / 4)
      rw [← Real.rpow_mul hN0.le] at this
      calc N ^ (-(c'' / 4)) = N ^ (-c'' * (1 / 4)) := by ring_nf
        _ ≤ p := this
    have hpε : N ^ (-(c'' / 4 * ε)) ≤ p ^ ε := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hpge hε.le
      rw [← Real.rpow_mul hN0.le] at this
      calc N ^ (-(c'' / 4 * ε)) = N ^ (-(c'' / 4) * ε) := by ring_nf
        _ ≤ p ^ ε := this
    set Ks := Cs * Q with hKs_def
    have hC0 : (4 * (2 * Ks) + 5) * (8 * (2 * Ks) + 9) ≤ 325 * Ks ^ 2 := by nlinarith
    have hQ18 : Q ^ 18 = N ^ (306 * η) := by
      rw [hQ_def, rpow_mul_nat hN0]; push_cast; ring_nf
    have hden : 5 * ((4 * (2 * Ks) + 5) * (8 * (2 * Ks) + 9)) * (36864 * Ks ^ 16) ≤
        N ^ (ε₁ - c'' / 4 * ε) := by
      calc 5 * ((4 * (2 * Ks) + 5) * (8 * (2 * Ks) + 9)) * (36864 * Ks ^ 16)
          ≤ 5 * (325 * Ks ^ 2) * (36864 * Ks ^ 16) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
        _ = 5 * 325 * 36864 * Cs ^ 18 * Q ^ 18 := by rw [hKs_def]; ring
        _ = 5 * 325 * 36864 * Cs ^ 18 * N ^ (306 * η) := by rw [hQ18]
        _ ≤ N ^ (ε₁ - c'' / 4 * ε) := hf
    have hden0 : 0 < 5 * ((4 * (2 * Ks) + 5) * (8 * (2 * Ks) + 9)) * (36864 * Ks ^ 16) := by
      positivity
    have hkey : N ^ (-ε₁) ≤ p ^ ε /
        (5 * ((4 * (2 * Ks) + 5) * (8 * (2 * Ks) + 9)) * (36864 * Ks ^ 16)) := by
      rw [le_div_iff₀ hden0]
      calc N ^ (-ε₁) * (5 * ((4 * (2 * Ks) + 5) * (8 * (2 * Ks) + 9)) * (36864 * Ks ^ 16))
          ≤ N ^ (-ε₁) * N ^ (ε₁ - c'' / 4 * ε) :=
            mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hN0.le _)
        _ = N ^ (-(c'' / 4 * ε)) := by rw [← Real.rpow_add hN0]; ring_nf
        _ ≤ p ^ ε := hpε
    calc N ^ (-ε₁) * H = H * N ^ (-ε₁) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hkey hH0.le

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
