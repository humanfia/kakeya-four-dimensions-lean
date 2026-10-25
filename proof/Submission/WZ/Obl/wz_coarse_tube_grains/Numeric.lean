-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.Numeric.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Exponent bookkeeping for the single-tube grains theorem

Elementary inequalities between powers of `δ`, used by `Main.lean`.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.Num

theorem rpow_le_of_le {δ a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hab : b ≤ a) :
    δ ^ a ≤ δ ^ b :=
  Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hab

/-- Consequences of the Córdoba count for the prescribed length `c`. -/
theorem c_facts {δ ρ c ε τ ηc m : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ)
    (hm1 : 1 ≤ m) (hηc : ηc ≤ ε / 4) (hε : 0 < ε)
    (hcord : δ ^ ηc * ρ ≤ 4096 * m * δ) (hc1 : δ ^ (1 - τ) / ρ ≤ c)
    (hc2 : c ≤ δ ^ ε * (ρ / δ) / m)
    (hs1 : 16384 * δ ^ (3 * ε / 4) ≤ 1) (hs2 : 2097152 * δ ^ τ ≤ 1) :
    0 < c ∧ c ≤ 4096 * δ ^ (3 * ε / 4) ∧ c ≤ 1 / 4 ∧ δ / ρ ≤ 4096 * δ ^ τ ∧ 512 * δ ≤ ρ ∧
      16 * δ ≤ 128 * (ρ / 256) * c := by
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hc1
  have hm0 : 0 < m := by linarith
  have hc_pow : c ≤ 4096 * δ ^ (3 * ε / 4) := by
    have hp : 0 < δ ^ ηc := by positivity
    have h1 : ρ / δ / m ≤ 4096 * δ ^ (-ηc) := by
      rw [Real.rpow_neg hδ.le, div_div, div_le_iff₀ (by positivity)]
      have h3 : ρ ≤ 4096 * m * δ / δ ^ ηc := by
        rw [le_div_iff₀ hp]; linarith
      calc ρ ≤ 4096 * m * δ / δ ^ ηc := h3
        _ = 4096 * (δ ^ ηc)⁻¹ * (δ * m) := by field_simp
    have h2 : δ ^ ε * δ ^ (-ηc) ≤ δ ^ (3 * ε / 4) := by
      rw [← Real.rpow_add hδ]
      exact rpow_le_of_le hδ hδ1 (by linarith)
    calc c ≤ δ ^ ε * (ρ / δ) / m := hc2
      _ = δ ^ ε * (ρ / δ / m) := by ring
      _ ≤ δ ^ ε * (4096 * δ ^ (-ηc)) := by gcongr
      _ = 4096 * (δ ^ ε * δ ^ (-ηc)) := by ring
      _ ≤ 4096 * δ ^ (3 * ε / 4) := by gcongr
  have hc4 : c ≤ 1 / 4 := by linarith
  have hδ34 : δ ^ (3 * ε / 4) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have h1 : δ ^ (1 - τ) ≤ 4096 * ρ := by
    have h := hc1.trans (hc_pow.trans (by nlinarith : 4096 * δ ^ (3 * ε / 4) ≤ 4096))
    rw [div_le_iff₀ hρ] at h
    linarith
  have h2 : δ = δ ^ τ * δ ^ (1 - τ) := by
    rw [← Real.rpow_add hδ]; simp
  have hτpos : 0 < δ ^ τ := by positivity
  have hδρ : δ / ρ ≤ 4096 * δ ^ τ := by
    rw [div_le_iff₀ hρ]
    calc δ = δ ^ τ * δ ^ (1 - τ) := h2
      _ ≤ δ ^ τ * (4096 * ρ) := by gcongr
      _ = 4096 * δ ^ τ * ρ := by ring
  have h512 : 512 * δ ≤ ρ := by
    have h := hδρ
    rw [div_le_iff₀ hρ] at h
    nlinarith [mul_le_mul_of_nonneg_right hs2 hρ.le]
  have h16 : 16 * δ ≤ 128 * (ρ / 256) * c := by
    have h3 : δ ^ (1 - τ) ≤ ρ * c := by
      have h := hc1
      rw [div_le_iff₀ hρ] at h; linarith
    have h4 : 32 * δ ≤ δ ^ (1 - τ) := by
      have h5 : 32 * δ ^ τ ≤ 1 := by linarith
      calc 32 * δ = 32 * δ ^ τ * δ ^ (1 - τ) := by rw [mul_assoc, ← h2]
        _ ≤ 1 * δ ^ (1 - τ) := by gcongr
        _ = δ ^ (1 - τ) := one_mul _
    linarith
  exact ⟨hcpos, hc_pow, hc4, hδρ, h512, h16⟩

/-- The normalized radius of the thin carrier. -/
theorem xi_facts {δ ρ ξ τ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hξ : ξ = δ / (100 * (ρ / 256))) (hδρ : δ / ρ ≤ 4096 * δ ^ τ) :
    0 < ξ ∧ ξ ≤ 10486 * δ ^ τ ∧ δ ≤ ξ := by
  have hξeq : ξ = 64 / 25 * (δ / ρ) := by rw [hξ]; field_simp; ring
  have hτ0 : 0 ≤ δ ^ τ := Real.rpow_nonneg hδ.le _
  have hδρ1 : δ ≤ δ / ρ := le_div_self hδ.le hρ hρ1
  refine ⟨by rw [hξeq]; positivity, by rw [hξeq]; linarith, by rw [hξeq]; linarith⟩

theorem P5_fact {δ ξ c ε ζ : ℝ} (hδ : 0 < δ) (hδξ : δ ≤ ξ) (hζ : ζ = ε / 4) (hε : 0 < ε)
    (hc : c ≤ 4096 * δ ^ (3 * ε / 4)) (hs4 : 2560 * 4096 * δ ^ (7 * ε / 10) ≤ 1) :
    2560 * c ≤ ξ ^ (ζ / 5) := by
  have h1 : δ ^ (3 * ε / 4) = δ ^ (7 * ε / 10) * δ ^ (ε / 20) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have h2 : δ ^ (ε / 20) ≤ ξ ^ (ζ / 5) := by
    rw [hζ, show ε / 4 / 5 = ε / 20 by ring]
    exact Real.rpow_le_rpow hδ.le hδξ (by positivity)
  have h3 : 0 ≤ δ ^ (ε / 20) := Real.rpow_nonneg hδ.le _
  calc 2560 * c ≤ 2560 * (4096 * δ ^ (3 * ε / 4)) := by gcongr
    _ = (2560 * 4096 * δ ^ (7 * ε / 10)) * δ ^ (ε / 20) := by rw [h1]; ring
    _ ≤ 1 * δ ^ (ε / 20) := by gcongr
    _ ≤ ξ ^ (ζ / 5) := by rw [one_mul]; exact h2

theorem P6_fact {δ ξ τ D m C₀ : ℝ} (hδ : 0 < δ) (hξ0 : 0 < ξ) (hξ : ξ ≤ 10486 * δ ^ τ)
    (hτD : τ * D = 16) (hD : 0 < D) (hm0 : 0 ≤ m) (hm : m * δ ^ 6 ≤ C₀)
    (hs5 : C₀ * 10486 ^ D * δ ^ (10 : ℝ) ≤ 1) : m ≤ ξ ^ (-D) := by
  have hτpos : 0 < δ ^ τ := by positivity
  have h1 : (10486 * δ ^ τ) ^ (-D) ≤ ξ ^ (-D) :=
    Real.rpow_le_rpow_of_nonpos hξ0 hξ (by linarith)
  have hD0 : 0 < (10486 : ℝ) ^ D := by positivity
  have h2 : (10486 * δ ^ τ) ^ (-D) = ((10486 : ℝ) ^ D)⁻¹ * (δ ^ (16 : ℕ))⁻¹ := by
    rw [Real.mul_rpow (by norm_num) hτpos.le, ← Real.rpow_mul hδ.le,
      show τ * -D = -((16 : ℕ) : ℝ) by push_cast; linarith,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10486), Real.rpow_neg hδ.le, Real.rpow_natCast]
  have hs5' : C₀ * 10486 ^ D * δ ^ (10 : ℕ) ≤ 1 := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hs5
    exact hs5
  have hδ6 : 0 < δ ^ 6 := by positivity
  have hδ16 : 0 < δ ^ (16 : ℕ) := by positivity
  have h3 : m ≤ ((10486 : ℝ) ^ D)⁻¹ * (δ ^ (16 : ℕ))⁻¹ := by
    rw [← mul_inv, ← one_div, le_div_iff₀ (by positivity)]
    calc m * ((10486 : ℝ) ^ D * δ ^ (16 : ℕ)) = m * δ ^ 6 * ((10486 : ℝ) ^ D * δ ^ 10) := by
          ring
      _ ≤ C₀ * ((10486 : ℝ) ^ D * δ ^ 10) := by gcongr
      _ = C₀ * 10486 ^ D * δ ^ (10 : ℕ) := by ring
      _ ≤ 1 := hs5'
  rw [← h2] at h3
  exact h3.trans h1

theorem P7_fact {δ ξ ρ c m ε ζ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hm : 0 < m) (hδξ : δ ≤ ξ)
    (hζ : ζ = ε / 4) (hε : 0 < ε) (hc2 : c ≤ δ ^ ε * (ρ / δ) / m)
    (hs6 : 256 * δ ^ (19 * ε / 20) ≤ 1) :
    c * m * δ ≤ ξ ^ (ζ / 5) * (ρ / 256) := by
  have h1 : c * m * δ ≤ δ ^ ε * ρ := by
    have h := hc2
    rw [le_div_iff₀ hm] at h
    have e : δ ^ ε * (ρ / δ) * δ = δ ^ ε * ρ := by field_simp
    calc c * m * δ ≤ δ ^ ε * (ρ / δ) * δ := by gcongr
      _ = δ ^ ε * ρ := e
  have h2 : δ ^ ε = δ ^ (19 * ε / 20) * δ ^ (ε / 20) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have h3 : δ ^ (ε / 20) ≤ ξ ^ (ζ / 5) := by
    rw [hζ, show ε / 4 / 5 = ε / 20 by ring]
    exact Real.rpow_le_rpow hδ.le hδξ (by positivity)
  have h4 : 256 * δ ^ ε ≤ ξ ^ (ζ / 5) := by
    have h0 : 0 ≤ δ ^ (ε / 20) := Real.rpow_nonneg hδ.le _
    calc 256 * δ ^ ε = (256 * δ ^ (19 * ε / 20)) * δ ^ (ε / 20) := by rw [h2]; ring
      _ ≤ 1 * δ ^ (ε / 20) := by gcongr
      _ ≤ ξ ^ (ζ / 5) := by rw [one_mul]; exact h3
  calc c * m * δ ≤ δ ^ ε * ρ := h1
    _ = 256 * δ ^ ε * (ρ / 256) := by ring
    _ ≤ ξ ^ (ζ / 5) * (ρ / 256) := by gcongr

theorem broad_coef {δ ξ τ ηx η K₁ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hξ0 : 0 < ξ)
    (hξ : ξ ≤ 10486 * δ ^ τ) (hηx : 0 < ηx) (hηx1 : ηx ≤ 1) (hτ : 0 < τ)
    (hη : η ≤ τ * ηx / 64) (hK : 0 ≤ K₁)
    (hs8 : 10486 * K₁ * δ ^ (63 * τ * ηx / 64) ≤ 1) : K₁ * δ ^ (-η) ≤ ξ ^ (-ηx) := by
  have hτpos : 0 < δ ^ τ := by positivity
  have h1 : (10486 * δ ^ τ) ^ (-ηx) ≤ ξ ^ (-ηx) :=
    Real.rpow_le_rpow_of_nonpos hξ0 hξ (by linarith)
  have h2 : (10486 * δ ^ τ) ^ (-ηx) = 10486 ^ (-ηx) * δ ^ (-(τ * ηx)) := by
    rw [Real.mul_rpow (by norm_num) hτpos.le, ← Real.rpow_mul hδ.le]; ring_nf
  have h3 : (10486 : ℝ) ^ (-1 : ℝ) ≤ 10486 ^ (-ηx) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h6 : (10486 : ℝ) ^ (-1 : ℝ) = 1 / 10486 := by
    rw [Real.rpow_neg_one]; norm_num
  rw [h6] at h3
  have h4 : δ ^ (-η) = δ ^ (63 * τ * ηx / 64) * δ ^ (-(τ * ηx)) * δ ^ (τ * ηx / 64 - η) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
  have h5 : δ ^ (τ * ηx / 64 - η) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by linarith)
  have hpos : 0 ≤ δ ^ (-(τ * ηx)) := Real.rpow_nonneg hδ.le _
  have hq : 0 ≤ δ ^ (63 * τ * ηx / 64) := Real.rpow_nonneg hδ.le _
  have h7 : K₁ * δ ^ (-η) ≤ 1 / 10486 * δ ^ (-(τ * ηx)) := by
    rw [h4]
    calc K₁ * (δ ^ (63 * τ * ηx / 64) * δ ^ (-(τ * ηx)) * δ ^ (τ * ηx / 64 - η))
        ≤ K₁ * (δ ^ (63 * τ * ηx / 64) * δ ^ (-(τ * ηx)) * 1) := by gcongr
      _ = (10486 * K₁ * δ ^ (63 * τ * ηx / 64)) * (1 / 10486 * δ ^ (-(τ * ηx))) := by ring
      _ ≤ 1 * (1 / 10486 * δ ^ (-(τ * ηx))) := by gcongr
      _ = 1 / 10486 * δ ^ (-(τ * ηx)) := one_mul _
  calc K₁ * δ ^ (-η) ≤ 1 / 10486 * δ ^ (-(τ * ηx)) := h7
    _ ≤ 10486 ^ (-ηx) * δ ^ (-(τ * ηx)) := mul_le_mul_of_nonneg_right h3 hpos
    _ = (10486 * δ ^ τ) ^ (-ηx) := h2.symm
    _ ≤ ξ ^ (-ηx) := h1

theorem dens_coef {δ ξ τ ηx η K₁ ν lg : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hξ0 : 0 < ξ)
    (hξ : ξ ≤ 10486 * δ ^ τ) (hηx : 0 < ηx) (hηx1 : ηx ≤ 1) (hτ : 0 < τ)
    (hη : η ≤ τ * ηx / 64) (hν : ν = τ * ηx / 32) (hlg : lg ≤ δ ^ (-ν)) (hlg0 : 0 ≤ lg)
    (hs7 : 10486 * K₁ ^ 2 * δ ^ (13 * τ * ηx / 64) ≤ 1) :
    ξ ^ (ηx / 4) * (K₁ ^ 2 * lg) ≤ δ ^ η := by
  have hτpos : 0 < δ ^ τ := by positivity
  have h1 : ξ ^ (ηx / 4) ≤ 10486 * δ ^ (τ * ηx / 4) := by
    calc ξ ^ (ηx / 4) ≤ (10486 * δ ^ τ) ^ (ηx / 4) :=
          Real.rpow_le_rpow hξ0.le hξ (by positivity)
      _ = 10486 ^ (ηx / 4) * δ ^ (τ * ηx / 4) := by
          rw [Real.mul_rpow (by norm_num) hτpos.le, ← Real.rpow_mul hδ.le]; ring_nf
      _ ≤ 10486 * δ ^ (τ * ηx / 4) := by
          gcongr
          exact Real.rpow_le_self_of_one_le (by norm_num) (by linarith)
  have h2 : δ ^ (τ * ηx / 4) * δ ^ (-ν) = δ ^ (13 * τ * ηx / 64) * δ ^ (τ * ηx / 64) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; rw [hν]; ring
  have h3 : δ ^ (τ * ηx / 64) ≤ δ ^ η := rpow_le_of_le hδ hδ1 hη
  have hK2 : 0 ≤ K₁ ^ 2 := sq_nonneg _
  have hp1 : 0 ≤ δ ^ (τ * ηx / 64) := Real.rpow_nonneg hδ.le _
  have hp2 : 0 ≤ ξ ^ (ηx / 4) := Real.rpow_nonneg hξ0.le _
  calc ξ ^ (ηx / 4) * (K₁ ^ 2 * lg)
      ≤ (10486 * δ ^ (τ * ηx / 4)) * (K₁ ^ 2 * δ ^ (-ν)) := by gcongr
    _ = (10486 * K₁ ^ 2 * δ ^ (13 * τ * ηx / 64)) * δ ^ (τ * ηx / 64) := by
        rw [show (10486 * δ ^ (τ * ηx / 4)) * (K₁ ^ 2 * δ ^ (-ν)) =
          10486 * K₁ ^ 2 * (δ ^ (τ * ηx / 4) * δ ^ (-ν)) by ring, h2]; ring
    _ ≤ 1 * δ ^ (τ * ηx / 64) := by gcongr
    _ ≤ δ ^ η := by rw [one_mul]; exact h3

theorem lambda_small {δ ξ ε ηx ν ζ τ K₁ Kx lg : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδξ : δ ≤ ξ) (hζ : ζ = ε / 4) (hν : ν = τ * ηx / 32) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hηx : 0 < ηx) (hηxζ : ηx ≤ ζ / 48) (hε : 0 < ε) (hlg : lg ≤ δ ^ (-ν)) (hlg0 : 0 ≤ lg)
    (hKx : 0 ≤ Kx) (hs9 : 4 * K₁ ^ 2 * Kx * δ ^ (ε / 5) ≤ 1) :
    4 * (K₁ ^ 2 * lg * (Kx * ξ ^ (-(ηx / 8))) * δ ^ (-ζ)) * δ ^ (ε / 2) ≤ 1 := by
  have hξ0 : 0 < ξ := lt_of_lt_of_le hδ hδξ
  have hξ8 : ξ ^ (-(ηx / 8)) ≤ δ ^ (-(ηx / 8)) :=
    Real.rpow_le_rpow_of_nonpos hδ hδξ (by linarith)
  have hηx' : ηx ≤ ε / 192 := by rw [hζ] at hηxζ; linarith
  have hexp : ε / 5 ≤ -ν + (-(ηx / 8) + (-ζ + ε / 2)) := by
    rw [hν, hζ]
    have : τ * ηx ≤ ηx := by nlinarith
    linarith
  have hprod : δ ^ (-ν) * (δ ^ (-(ηx / 8)) * (δ ^ (-ζ) * δ ^ (ε / 2))) ≤ δ ^ (ε / 5) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    exact rpow_le_of_le hδ hδ1 hexp
  have hK2 : 0 ≤ K₁ ^ 2 := sq_nonneg _
  have hp1 : 0 ≤ δ ^ (-ζ) := Real.rpow_nonneg hδ.le _
  have hp2 : 0 ≤ δ ^ (ε / 2) := Real.rpow_nonneg hδ.le _
  have hp3 : 0 ≤ ξ ^ (-(ηx / 8)) := Real.rpow_nonneg hξ0.le _
  calc 4 * (K₁ ^ 2 * lg * (Kx * ξ ^ (-(ηx / 8))) * δ ^ (-ζ)) * δ ^ (ε / 2)
      ≤ 4 * (K₁ ^ 2 * δ ^ (-ν) * (Kx * δ ^ (-(ηx / 8))) * δ ^ (-ζ)) * δ ^ (ε / 2) := by
        gcongr
    _ = 4 * K₁ ^ 2 * Kx * (δ ^ (-ν) * (δ ^ (-(ηx / 8)) * (δ ^ (-ζ) * δ ^ (ε / 2)))) := by ring
    _ ≤ 4 * K₁ ^ 2 * Kx * δ ^ (ε / 5) := by gcongr
    _ ≤ 1 := hs9

end WangZahlLot.Obl.wz_coarse_tube_grains.Num
