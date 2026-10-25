/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarDyadicPowerRanges.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarDyadicPowerRanges.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDyadicBridge
import Mathlib.Tactic.FieldSimp

/-! Original factor-K dyadic readings lie in one fixed compact power range. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

theorem scalar_factor_power_range {N K a b γ q : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (ha : 0 < a) (hab : a ≤ b)
    (hγa : a ≤ γ) (hγb : γ ≤ b) (hKN : K ≤ N ^ (a / 4))
    (hlow : N ^ (-γ) / K ≤ q) (hhigh : q ≤ K * N ^ (-γ)) :
    N ^ (-(2 * b)) ≤ q ∧ q ≤ N ^ (-(a / 2)) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  constructor
  · calc
      _ ≤ N ^ (-γ - a / 4) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ ≤ N ^ (-γ) / K := by
        apply (le_div_iff₀ hKpos).mpr
        calc
          _ ≤ N ^ (-γ - a / 4) * N ^ (a / 4) :=
            mul_le_mul_of_nonneg_left hKN (Real.rpow_nonneg hNpos.le _)
          _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring
      _ ≤ _ := hlow
  · calc
      _ ≤ K * N ^ (-γ) := hhigh
      _ ≤ N ^ (a / 4) * N ^ (-γ) :=
        mul_le_mul_of_nonneg_right hKN (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (a / 4 - γ) := by
        rw [← Real.rpow_add hNpos]
        congr 1
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem scalar_dyadic_height_ratio_of_power_range {N a b : ℝ} {top start : ℕ}
    (hN : 1 ≤ N) (ha : 0 < a) (hab : a ≤ b)
    (htop : N ^ (-(2 * b)) ≤ scalarDyadicLength top)
    (hstart : scalarDyadicLength start ≤ N ^ (-(a / 2))) :
    (top : ℝ) ≤ (4 * b / a) * start := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hb : 0 < b := ha.trans_le hab
  have hratio : 0 ≤ 4 * b / a := by positivity
  have hp := Real.rpow_le_rpow (scalarDyadicLength_pos start).le hstart hratio
  have he : (N ^ (-(a / 2))) ^ (4 * b / a) = N ^ (-(2 * b)) := by
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    field_simp
    ring
  rw [he] at hp
  have hh := hp.trans htop
  change ((2 : ℝ) ^ (-(start : ℝ))) ^ (4 * b / a) ≤ (2 : ℝ) ^ (-(top : ℝ)) at hh
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
  have h := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hh
  nlinarith

theorem scalar_floor_square_of_power_range {N b ζ H : ℝ}
    (hN : 0 < N) (hζ : ζ ≤ N ^ (-(4 * b))) (hH : N ^ (-(2 * b)) ≤ H) : ζ ≤ H ^ 2 := by
  have hpow : (N ^ (-(2 * b))) ^ (2 : ℕ) = N ^ (-(4 * b)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    norm_num
    ring
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hN.le (-(2 * b))) hH 2
  rw [hpow] at hh
  exact hζ.trans hh

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
