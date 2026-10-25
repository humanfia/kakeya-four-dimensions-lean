import Mathlib

/-! Explicit budgets for the normalized-packet recovery step. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

/-- The base-cell ceiling and the retained original mass give the required
positive-volume witness budget with this choice of `η`. -/
theorem packet_recovery_witness_budget {H L m b : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hmb : m / H ≤ b) :
    (4 * H) ^ 2 * (H * m) * (1 / (256 * H ^ 4 * L ^ 4)) ≤
      (L⁻¹ / 2) ^ 4 * b := by
  have heq : (4 * H) ^ 2 * (H * m) * (1 / (256 * H ^ 4 * L ^ 4)) =
      (L⁻¹ / 2) ^ 4 * (m / H) := by
    field_simp
    <;> ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hmb (by positivity)

/-- All the physical-to-normalized transfer distances are below the improved
error scale, uniformly over the fine exponent choices in the certificate. -/
theorem packet_recovery_transfer_le {N H h κ c Z B : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hh : 0 < h) (hscale : N ^ (-κ) / H ≤ h)
    (hκ : κ ≤ 1) (hc : c ≤ 1) (hZ : 10 ≤ Z) (hB : Z + 10 ≤ B) :
    N ^ (-Z) / (4 * H) + N ^ (-B) / (4 * H * h) + N ^ (-B) ≤
      3 * N ^ (-1 - c) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hcoarse : N ^ (-Z) ≤ N ^ (-1 - c) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hfine : N ^ (-B) ≤ N ^ (-1 - c) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hfirst : N ^ (-Z) / (4 * H) ≤ N ^ (-1 - c) :=
    (div_le_self (Real.rpow_nonneg hNpos.le _) (by linarith : 1 ≤ 4 * H)).trans hcoarse
  have hden : N ^ (-κ) ≤ 4 * H * h := by
    have h := (div_le_iff₀ hHpos).mp hscale
    nlinarith [mul_pos hHpos hh]
  have hsecond : N ^ (-B) / (4 * H * h) ≤ N ^ (-1 - c) := by
    calc
      N ^ (-B) / (4 * H * h) ≤ N ^ (-B) / N ^ (-κ) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hNpos.le _)
          (Real.rpow_pos_of_pos hNpos _) hden
      _ = N ^ (κ - B) := by rw [← Real.rpow_sub hNpos]; congr 1; ring
      _ ≤ N ^ (-1 - c) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  linarith

/-- A single fixed polynomial loss bounds the entire recovery error. The only
remaining angular cost is the explicit factor `N^(18*r)`. -/
theorem packet_recovery_error_le (D : ℕ) {N H L h κ c Z B r C₀ C₁ Cₜ : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hHL : H ≤ L) (hh : 0 < h)
    (hscale : N ^ (-κ) / H ≤ h) (hκ : κ ≤ 1) (hc : c ≤ 1)
    (hZ : 10 ≤ Z) (hB : Z + 10 ≤ B) (hr : 0 ≤ r)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCₜ : 0 ≤ Cₜ) :
    H * N ^ (-1 - c) +
      C₀ * (L / N ^ (-r)) ^ 18 *
        (16 * ((D : ℝ) + 1) / (1 / (256 * H ^ 4 * L ^ 4))) ^ (2 * D) *
        (Cₜ * H ^ 3 * (H * N ^ (-1 - c)) + C₁ * L ^ (2 * D + 4) *
          (N ^ (-Z) / (4 * H) + N ^ (-B) / (4 * H * h) + N ^ (-B))) ≤
      (1 + C₀ * (4096 * ((D : ℝ) + 1)) ^ (2 * D) * (Cₜ + 3 * C₁)) *
        L ^ (18 * D + 22) * N ^ (18 * r) * N ^ (-1 - c) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hL : 1 ≤ L := hH.trans hHL
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have ht := packet_recovery_transfer_le hN hH hh hscale hκ hc hZ hB
  have hcoeff : H ^ 4 ≤ L ^ (2 * D + 4) :=
    (pow_le_pow_left₀ hH0 hHL 4).trans (pow_le_pow_right₀ hL (by omega))
  have hbracket : Cₜ * H ^ 3 * (H * N ^ (-1 - c)) + C₁ * L ^ (2 * D + 4) *
      (N ^ (-Z) / (4 * H) + N ^ (-B) / (4 * H * h) + N ^ (-B)) ≤
        (Cₜ + 3 * C₁) * L ^ (2 * D + 4) * N ^ (-1 - c) := by
    calc
      _ = Cₜ * H ^ 4 * N ^ (-1 - c) + C₁ * L ^ (2 * D + 4) *
          (N ^ (-Z) / (4 * H) + N ^ (-B) / (4 * H * h) + N ^ (-B)) := by ring
      _ ≤ Cₜ * L ^ (2 * D + 4) * N ^ (-1 - c) +
          C₁ * L ^ (2 * D + 4) * (3 * N ^ (-1 - c)) := by
        gcongr
      _ = _ := by ring
  have hremez :
      (16 * ((D : ℝ) + 1) / (1 / (256 * H ^ 4 * L ^ 4))) ^ (2 * D) ≤
        (4096 * ((D : ℝ) + 1)) ^ (2 * D) * L ^ (16 * D) := by
    have hbase : 16 * ((D : ℝ) + 1) / (1 / (256 * H ^ 4 * L ^ 4)) ≤
        (4096 * ((D : ℝ) + 1)) * L ^ 8 := by
      rw [div_eq_mul_inv, one_div, inv_inv]
      calc
        _ = (4096 * ((D : ℝ) + 1)) * (H ^ 4 * L ^ 4) := by ring
        _ ≤ (4096 * ((D : ℝ) + 1)) * (L ^ 4 * L ^ 4) := by gcongr
        _ = _ := by ring
    have hpow := pow_le_pow_left₀ (by positivity :
      0 ≤ 16 * ((D : ℝ) + 1) / (1 / (256 * H ^ 4 * L ^ 4))) hbase (2 * D)
    simpa only [mul_pow, ← pow_mul, show 8 * (2 * D) = 16 * D by omega] using hpow
  have hangular : (L / N ^ (-r)) ^ 18 = L ^ 18 * N ^ (18 * r) := by
    rw [Real.rpow_neg hNpos.le, div_eq_mul_inv, inv_inv, mul_pow]
    congr 1
    rw [← Real.rpow_natCast (N ^ r) 18, ← Real.rpow_mul hNpos.le]
    congr 1
    norm_num
    ring
  have hhigh : H ≤ L ^ (18 * D + 22) :=
    hHL.trans (by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ 18 * D + 22 by omega))
  have hangle1 : 1 ≤ N ^ (18 * r) := Real.one_le_rpow hN (by positivity)
  have hfirst : H * N ^ (-1 - c) ≤ L ^ (18 * D + 22) * N ^ (18 * r) * N ^ (-1 - c) := by
    gcongr
    exact le_mul_of_one_le_right (by positivity) hangle1 |>.trans' hhigh
  calc
    _ ≤ L ^ (18 * D + 22) * N ^ (18 * r) * N ^ (-1 - c) +
        C₀ * (L ^ 18 * N ^ (18 * r)) *
          ((4096 * ((D : ℝ) + 1)) ^ (2 * D) * L ^ (16 * D)) *
          ((Cₜ + 3 * C₁) * L ^ (2 * D + 4) * N ^ (-1 - c)) := by
      rw [hangular]
      exact add_le_add hfirst (mul_le_mul_of_nonneg_left hbracket (by positivity) |>.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hremez (by positivity)) (by positivity)))
    _ = _ := by
      have he : L ^ (18 * D + 22) = L ^ 18 * L ^ (16 * D) * L ^ (2 * D + 4) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      rw [he]
      ring

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
