-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.BrowNumerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The MK4 row constant below `K` (session x1088).

* `mk4Kg_le`: `mk4Kg κ Vmax Kc Cband c fr δL N ≤ 2^18 P³ Q Kc^301 Y³` once `κ, Vmax, c⁻¹ ≤ P`,
  `Cband ≤ Q`, `4 (Vmax+1) κ N^(2δL)/fr ≤ Y` (`P, Q, Y ≥ 1`).
* `eventually_brow_le`: at the MK4 choices of the sample (`Vmax = 2 K_d`, `c = κ⁻¹/512`, the
  literal band constant `Cband` of `sample_final`'s `hKgCount` with `perror = δ₀ L`, the front radius
  `N^(-ub L)`) and any census constant `Kc ≤ N^(ρc L)`,
  `28 Kg^6 ≤ N^(D L)` eventually, uniformly in `κ, K_d ≤ N^σ` and `τ ≤ δ₀ L`, under the
  pre-sample rate inequality `72 δ₀ + 1806 ρc + 18 ub ≤ (98/100) D`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MK4Numerics

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- **The MK4 row constant**, crudely. -/
theorem mk4Kg_le {κ Vmax Kc Cband c fr δL N P Q Y : ℝ} (hκ : 1 ≤ κ) (hκP : κ ≤ P)
    (hV0 : 0 ≤ Vmax) (hVP : Vmax ≤ P) (hc : 0 < c) (hcP : c⁻¹ ≤ P) (hKc : 1 ≤ Kc)
    (hCb0 : 0 ≤ Cband) (hCbQ : Cband ≤ Q) (hQ : 1 ≤ Q)
    (hY : (4 * (Vmax + 1) * κ * N ^ (2 * δL) / fr) ^ 3 ≤ Y ^ 3) (hY1 : 1 ≤ Y) :
    mk4Kg κ Vmax Kc Cband c fr δL N ≤ 2 ^ 18 * P ^ 3 * Q * Kc ^ 301 * Y ^ 3 := by
  have hP1 : 1 ≤ P := hκ.trans hκP
  have hP0 : 0 ≤ P := by linarith
  have hP2 : P ≤ P ^ 2 := le_self_pow₀ hP1 (by norm_num)
  have hP23 : P ^ 2 ≤ P ^ 3 := pow_le_pow_right₀ hP1 (by norm_num)
  have hKc301 : 1 ≤ Kc ^ 301 := one_le_pow₀ hKc
  have hY3 : 1 ≤ Y ^ 3 := one_le_pow₀ hY1
  have hQKY : 1 ≤ Q * Kc ^ 301 * Y ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hQ hKc301) hY3
  have hbase : 1 + 24 * κ + κ ^ 2 + Vmax ≤ 27 * P ^ 2 := by
    have hκ2 : κ ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (by linarith) hκP 2
    nlinarith
  have hbase0 : 0 ≤ 1 + 24 * κ + κ ^ 2 + Vmax := by positivity
  have hB : 0 ≤ 2 ^ 18 * P ^ 3 := by positivity
  have hBig : 2 ^ 18 * P ^ 3 ≤ 2 ^ 18 * P ^ 3 * Q * Kc ^ 301 * Y ^ 3 := by
    have := mul_le_mul_of_nonneg_left hQKY hB
    calc 2 ^ 18 * P ^ 3 = 2 ^ 18 * P ^ 3 * 1 := by ring
      _ ≤ 2 ^ 18 * P ^ 3 * (Q * Kc ^ 301 * Y ^ 3) := this
      _ = _ := by ring
  unfold mk4Kg
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · -- the jet constant
    calc 6 * (1 + 24 * κ + κ ^ 2 + Vmax) ≤ 6 * (27 * P ^ 3) := by nlinarith
      _ ≤ 2 ^ 18 * P ^ 3 := by nlinarith
      _ ≤ _ := hBig
  · -- the duration constant
    rw [div_eq_mul_inv]
    calc (3 * (1 + 24 * κ + κ ^ 2 + Vmax) + 3) * 7 ^ 4 * c⁻¹
        ≤ (3 * (27 * P ^ 2) + 3 * P ^ 2) * 7 ^ 4 * P := by
          apply mul_le_mul _ hcP (inv_pos.mpr hc).le (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          have : (3 : ℝ) ≤ 3 * P ^ 2 := by nlinarith
          linarith
      _ = 201684 * (P ^ 2 * P) := by ring
      _ ≤ 2 ^ 18 * P ^ 3 := by
          have : P ^ 2 * P = P ^ 3 := by ring
          rw [this]; nlinarith [pow_nonneg hP0 3]
      _ ≤ _ := hBig
  · -- the count constant
    have hs := (two_pow_stepsOf hKc).2
    have hs0 : 0 ≤ (2 : ℝ) ^ stepsOf Kc := by positivity
    have hs3 : ((2 : ℝ) ^ stepsOf Kc) ^ 3 ≤ (2 * Kc ^ (100 : ℕ)) ^ 3 := pow_le_pow_left₀ hs0 hs 3
    rw [div_eq_mul_inv]
    calc 8 * Cband * (Kc * ((2 : ℝ) ^ stepsOf Kc) ^ 3) * c⁻¹
        ≤ 8 * Q * (Kc * (2 * Kc ^ (100 : ℕ)) ^ 3) * P := by
          apply mul_le_mul _ hcP (inv_pos.mpr hc).le (by positivity)
          apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hs3 (by linarith)
      _ = 64 * P * Q * Kc ^ 301 := by ring
      _ ≤ 2 ^ 18 * P ^ 3 * Q * Kc ^ 301 * Y ^ 3 := by
          have h1 : 64 * P ≤ 2 ^ 18 * P ^ 3 := by nlinarith [pow_nonneg hP0 3]
          have h2 : 0 ≤ Q * Kc ^ 301 := by positivity
          calc 64 * P * Q * Kc ^ 301 = 64 * P * (Q * Kc ^ 301) * 1 := by ring
            _ ≤ 2 ^ 18 * P ^ 3 * (Q * Kc ^ 301) * Y ^ 3 := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right h1 h2) hY3 (by norm_num)
                positivity
            _ = _ := by ring
  · -- the strip constant
    calc (4 * (Vmax + 1) * κ * N ^ (2 * δL) / fr) ^ 3 ≤ Y ^ 3 := hY
      _ ≤ 2 ^ 18 * P ^ 3 * Q * Kc ^ 301 * Y ^ 3 := by
          have h1 : 1 ≤ 2 ^ 18 * P ^ 3 * Q * Kc ^ 301 := by
            have := one_le_pow₀ (n := 3) hP1
            have h2 : (1 : ℝ) ≤ 2 ^ 18 := by norm_num
            have h3 : 1 ≤ 2 ^ 18 * P ^ 3 := one_le_mul_of_one_le_of_one_le h2 this
            exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h3 hQ) hKc301
          nlinarith

/-- **`Brow = 28 Kg^6 ≤ N^(D L)`, eventually.** -/
theorem eventually_brow_le (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) {L δ₀ ub ρc D d₁ : ℝ}
    (hL : 0 < L) (hδ : 0 ≤ δ₀) (hub : 0 ≤ ub) (hρc : 0 ≤ ρc) (hD : 0 < D) (hd₁ : d₁ ≤ 1)
    (hrate : 72 * δ₀ + 1806 * ρc + 18 * ub ≤ 98 / 100 * D) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ Kd Kc τ : ℝ, 1 ≤ κ → κ ≤ N k ^ σ → 1 ≤ Kd → Kd ≤ N k ^ σ → 1 ≤ Kc →
        Kc ≤ N k ^ (ρc * L) → 0 ≤ τ → τ ≤ δ₀ * L →
        28 * mk4Kg κ (2 * Kd) Kc (64 * (max κ Kd) ^ 2 * κ * 4 ^ d₁ *
            N k ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + τ)) (κ⁻¹ / 512) (N k ^ (-(ub * L)))
            (δ₀ * L) (N k) ^ 6 ≤ N k ^ (D * L) := by
  have hDL : 0 < D * L := mul_pos hD hL
  refine ⟨min 1 (D * L / 7200), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  set σ := min 1 (D * L / 7200) with hσdef
  have hσ0 : 0 < σ := lt_min one_pos (by positivity)
  have hσ1 : σ ≤ D * L / 7200 := min_le_right _ _
  have hN1 : ∀ᶠ k in atTop, 1 ≤ N k := hN.eventually (eventually_ge_atTop 1)
  have hbig : ∀ᶠ k in atTop, (2 : ℝ) ^ 389 ≤ N k ^ (D * L / 100) :=
    ((tendsto_rpow_atTop (by positivity : 0 < D * L / 100)).comp hN).eventually
      (eventually_ge_atTop _)
  filter_upwards [hN1, hbig] with k hk hbk
  intro κ Kd Kc τ hκ hκN hKd hKdN hKc hKcN hτ0 hτ
  set M := N k with hM
  have hMp : 0 < M := by linarith
  set X := M ^ σ with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hk hσ0.le
  have hX0 : 0 < X := by linarith
  -- the bounds `P`, `Q`, `Y`
  have hκ0 : 0 < κ := by linarith
  have hcP : (κ⁻¹ / 512)⁻¹ ≤ 512 * X := by
    rw [inv_div, div_inv_eq_mul]; linarith
  have hE6 : M ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + τ) ≤ M ^ (6 * δ₀ * L) :=
    Real.rpow_le_rpow_of_exponent_le hk (by nlinarith)
  have hmax : max κ Kd ≤ X := max_le hκN hKdN
  have hmax0 : 0 ≤ max κ Kd := hκ0.le.trans (le_max_left _ _)
  have h4d : (4 : ℝ) ^ d₁ ≤ 4 := by
    calc (4 : ℝ) ^ d₁ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hd₁
      _ = 4 := Real.rpow_one 4
  have hE60 : 0 ≤ M ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + τ) := (Real.rpow_pos_of_pos hMp _).le
  have hCb : 64 * (max κ Kd) ^ 2 * κ * 4 ^ d₁ * M ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + τ) ≤
      256 * X ^ 3 * M ^ (6 * δ₀ * L) := by
    have hm2 : (max κ Kd) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hmax0 hmax 2
    calc 64 * (max κ Kd) ^ 2 * κ * 4 ^ d₁ * M ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + τ)
        ≤ 64 * X ^ 2 * X * 4 * M ^ (6 * δ₀ * L) := by gcongr
      _ = 256 * X ^ 3 * M ^ (6 * δ₀ * L) := by ring
  have hQ1 : 1 ≤ 256 * X ^ 3 * M ^ (6 * δ₀ * L) := by
    have h1 : 1 ≤ X ^ 3 := one_le_pow₀ hX1
    have h2 : 1 ≤ M ^ (6 * δ₀ * L) := Real.one_le_rpow hk (by positivity)
    have := one_le_mul_of_one_le_of_one_le h1 h2
    nlinarith
  have hYb : (4 * (2 * Kd + 1) * κ * M ^ (2 * (δ₀ * L)) / M ^ (-(ub * L))) ^ 3 ≤
      (12 * X ^ 2 * M ^ ((2 * δ₀ + ub) * L)) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    have hdiv : 4 * (2 * Kd + 1) * κ * M ^ (2 * (δ₀ * L)) / M ^ (-(ub * L)) =
        4 * (2 * Kd + 1) * κ * (M ^ (2 * (δ₀ * L)) * M ^ (ub * L)) := by
      rw [Real.rpow_neg hMp.le, div_inv_eq_mul]; ring
    have hsplit : M ^ ((2 * δ₀ + ub) * L) = M ^ (2 * (δ₀ * L)) * M ^ (ub * L) := by
      rw [← Real.rpow_add hMp]; ring_nf
    rw [hdiv, hsplit]
    have h3 : 2 * Kd + 1 ≤ 3 * X := by linarith
    have hpow0 : 0 ≤ M ^ (2 * (δ₀ * L)) * M ^ (ub * L) := by positivity
    calc 4 * (2 * Kd + 1) * κ * (M ^ (2 * (δ₀ * L)) * M ^ (ub * L))
        ≤ 4 * (3 * X) * X * (M ^ (2 * (δ₀ * L)) * M ^ (ub * L)) := by gcongr
      _ = 12 * X ^ 2 * (M ^ (2 * (δ₀ * L)) * M ^ (ub * L)) := by ring
  have hY1 : 1 ≤ 12 * X ^ 2 * M ^ ((2 * δ₀ + ub) * L) := by
    have h1 : 1 ≤ X ^ 2 := one_le_pow₀ hX1
    have h2 : 1 ≤ M ^ ((2 * δ₀ + ub) * L) := Real.one_le_rpow hk (by positivity)
    have := one_le_mul_of_one_le_of_one_le h1 h2
    nlinarith
  have hKg := mk4Kg_le (P := 512 * X) hκ (by linarith) (by linarith) (by linarith)
    (by positivity) hcP hKc (by positivity) hCb hQ1 hYb hY1 (Kc := Kc) (fr := M ^ (-(ub * L)))
  -- the exponent bookkeeping
  have hKcp : Kc ^ 301 ≤ M ^ (301 * (ρc * L)) := by
    calc Kc ^ 301 ≤ (M ^ (ρc * L)) ^ 301 := pow_le_pow_left₀ (by linarith) hKcN 301
      _ = M ^ (301 * (ρc * L)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hMp.le]; ring_nf
  have hX3 : X ^ 3 = M ^ (3 * σ) := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hMp.le]; ring_nf
  have hX2 : X ^ 2 = M ^ (2 * σ) := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hMp.le]; ring_nf
  have hYp : (12 * X ^ 2 * M ^ ((2 * δ₀ + ub) * L)) ^ 3 =
      1728 * M ^ (6 * σ + 3 * ((2 * δ₀ + ub) * L)) := by
    rw [hX2, mul_pow, mul_pow, ← Real.rpow_natCast (M ^ (2 * σ)), ← Real.rpow_mul hMp.le,
      ← Real.rpow_natCast (M ^ ((2 * δ₀ + ub) * L)), ← Real.rpow_mul hMp.le, mul_assoc,
      ← Real.rpow_add hMp]
    norm_num; ring_nf
  have hbound : 2 ^ 18 * (512 * X) ^ 3 * (256 * X ^ 3 * M ^ (6 * δ₀ * L)) * Kc ^ 301 *
      (12 * X ^ 2 * M ^ ((2 * δ₀ + ub) * L)) ^ 3 ≤
      2 ^ 64 * M ^ (12 * σ + (12 * δ₀ + 3 * ub + 301 * ρc) * L) := by
    rw [hYp, mul_pow, hX3]
    have e : M ^ (12 * σ + (12 * δ₀ + 3 * ub + 301 * ρc) * L) =
        M ^ (3 * σ) * (M ^ (3 * σ) * M ^ (6 * δ₀ * L)) * M ^ (301 * (ρc * L)) *
          M ^ (6 * σ + 3 * ((2 * δ₀ + ub) * L)) := by
      rw [← Real.rpow_add hMp, ← Real.rpow_add hMp, ← Real.rpow_add hMp, ← Real.rpow_add hMp]
      ring_nf
    rw [e]
    have hpos1 : 0 ≤ M ^ (3 * σ) := (Real.rpow_pos_of_pos hMp _).le
    have hpos2 : 0 ≤ M ^ (6 * δ₀ * L) := (Real.rpow_pos_of_pos hMp _).le
    have hpos3 : 0 ≤ M ^ (6 * σ + 3 * ((2 * δ₀ + ub) * L)) := (Real.rpow_pos_of_pos hMp _).le
    calc 2 ^ 18 * (512 ^ 3 * M ^ (3 * σ)) * (256 * M ^ (3 * σ) * M ^ (6 * δ₀ * L)) * Kc ^ 301 *
          (1728 * M ^ (6 * σ + 3 * ((2 * δ₀ + ub) * L)))
        = (2 ^ 18 * 512 ^ 3 * 256 * 1728) * (M ^ (3 * σ) * (M ^ (3 * σ) * M ^ (6 * δ₀ * L)) *
            Kc ^ 301 * M ^ (6 * σ + 3 * ((2 * δ₀ + ub) * L))) := by ring
      _ ≤ 2 ^ 64 * (M ^ (3 * σ) * (M ^ (3 * σ) * M ^ (6 * δ₀ * L)) * M ^ (301 * (ρc * L)) *
            M ^ (6 * σ + 3 * ((2 * δ₀ + ub) * L))) := by
          apply mul_le_mul (by norm_num) _ (by positivity) (by norm_num)
          gcongr
  have hKg' := hKg.trans hbound
  have hKg0 : 0 ≤ mk4Kg κ (2 * Kd) Kc (64 * (max κ Kd) ^ 2 * κ * 4 ^ d₁ *
      M ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + τ)) (κ⁻¹ / 512) (M ^ (-(ub * L))) (δ₀ * L) M := by
    unfold mk4Kg
    exact le_trans (by positivity) (le_max_left _ _)
  have h6 := pow_le_pow_left₀ hKg0 hKg' 6
  have hpow6 : (2 ^ 64 * M ^ (12 * σ + (12 * δ₀ + 3 * ub + 301 * ρc) * L)) ^ 6 =
      2 ^ 384 * M ^ (72 * σ + (72 * δ₀ + 18 * ub + 1806 * ρc) * L) := by
    have e1 : ((2 : ℝ) ^ 64) ^ 6 = 2 ^ 384 := by rw [← pow_mul]
    have e2 : (M ^ (12 * σ + (12 * δ₀ + 3 * ub + 301 * ρc) * L)) ^ 6 =
        M ^ (72 * σ + (72 * δ₀ + 18 * ub + 1806 * ρc) * L) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hMp.le]
      congr 1; push_cast; ring
    rw [mul_pow, e1, e2]
  rw [hpow6] at h6
  have hexp : 72 * σ + (72 * δ₀ + 18 * ub + 1806 * ρc) * L + D * L / 100 ≤ D * L := by
    have : (72 * δ₀ + 18 * ub + 1806 * ρc) * L ≤ 98 / 100 * D * L :=
      mul_le_mul_of_nonneg_right (by linarith) hL.le
    linarith
  calc 28 * mk4Kg κ (2 * Kd) Kc (64 * (max κ Kd) ^ 2 * κ * 4 ^ d₁ *
        M ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + τ)) (κ⁻¹ / 512) (M ^ (-(ub * L))) (δ₀ * L) M ^ 6
      ≤ 28 * (2 ^ 384 * M ^ (72 * σ + (72 * δ₀ + 18 * ub + 1806 * ρc) * L)) := by
        linarith
    _ ≤ 2 ^ 389 * M ^ (72 * σ + (72 * δ₀ + 18 * ub + 1806 * ρc) * L) := by
        have h0 := (Real.rpow_pos_of_pos hMp (72 * σ + (72 * δ₀ + 18 * ub + 1806 * ρc) * L)).le
        have e : (2 : ℝ) ^ 389 = 2 ^ 5 * 2 ^ 384 := by rw [← pow_add]
        rw [e, ← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ h0
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        norm_num
    _ ≤ M ^ (D * L / 100) * M ^ (72 * σ + (72 * δ₀ + 18 * ub + 1806 * ρc) * L) :=
        mul_le_mul_of_nonneg_right hbk (Real.rpow_pos_of_pos hMp _).le
    _ = M ^ (72 * σ + (72 * δ₀ + 18 * ub + 1806 * ρc) * L + D * L / 100) := by
        rw [← Real.rpow_add hMp]; ring_nf
    _ ≤ M ^ (D * L) := Real.rpow_le_rpow_of_exponent_le hk hexp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
