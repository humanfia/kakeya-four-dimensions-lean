import Mathlib

/-!
Adapted from: here:o049

Original proof developed by session x0147 in
Submission/Obl/k4_cap_class_terminal_charts/FormatBounds.lean.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open Filter

/-- The atlas count has one fixed polynomial exponent before its loss is
chosen: `0 <= ε <= 1` only changes the constant and the eventual starting point. -/
theorem atlas_count_polynomial_bound {N D ρ C A B ε : ℝ}
    (hN : 1 ≤ N) (hD : 1 ≤ D) (hA : 0 ≤ A)
    (hDupper : D ≤ N ^ A) (hρ : N ^ (-B) ≤ ρ)
    (hC₀ : 0 ≤ C) (hC : C ≤ N) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1) :
    C * D ^ (2 + ε) / ρ ≤ N ^ Nat.ceil (1 + 3 * A + B) := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  have hρ₀ : 0 < ρ := (Real.rpow_pos_of_pos hN₀ (-B)).trans_le hρ
  have hDp : D ^ (2 + ε) ≤ N ^ (3 * A) := by
    calc
      _ ≤ (N ^ A) ^ (2 + ε) := Real.rpow_le_rpow hD₀.le hDupper (by linarith)
      _ = N ^ (A * (2 + ε)) := (Real.rpow_mul hN₀.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  have hprod : 1 ≤ ρ * N ^ B := by
    calc
      (1 : ℝ) = N ^ (-B) * N ^ B := by rw [← Real.rpow_add hN₀]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hρ (Real.rpow_nonneg hN₀.le _)
  have hinv : 1 / ρ ≤ N ^ B := (div_le_iff₀ hρ₀).mpr (by simpa only [mul_comm] using hprod)
  calc
    C * D ^ (2 + ε) / ρ = (C * D ^ (2 + ε)) * (1 / ρ) := by ring
    _ ≤ (N * N ^ (3 * A)) * N ^ B :=
      mul_le_mul (mul_le_mul hC hDp (Real.rpow_nonneg hD₀.le _) hN₀.le)
        hinv (by positivity) (by positivity)
    _ = N ^ (1 + 3 * A + B) := by
      calc
        _ = (N ^ (1 : ℝ) * N ^ (3 * A)) * N ^ B := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hN₀, ← Real.rpow_add hN₀]
    _ ≤ N ^ Nat.ceil (1 + 3 * A + B) := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hN (Nat.le_ceil (1 + 3 * A + B))

/-- Constants depending on the fixed tolerance are absorbed without changing
that polynomial exponent. -/
theorem eventually_atlas_count_bound (N D ρ count : ℕ → ℝ) {A B C ε : ℝ}
    (hN : Tendsto N atTop atTop) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hε₀ : 0 ≤ ε) (hε : ε ≤ 1)
    (hdata : ∀ᶠ k in atTop, 1 ≤ N k ∧ 1 ≤ D k ∧ D k ≤ N k ^ A ∧ N k ^ (-B) ≤ ρ k)
    (hcount : ∀ᶠ k in atTop, count k ≤ C * D k ^ (2 + ε) / ρ k) :
    ∀ᶠ k in atTop, count k ≤ N k ^ Nat.ceil (1 + 3 * A + B) := by
  filter_upwards [hN.eventually (eventually_ge_atTop C), hdata, hcount] with k hCN hk hc
  exact hc.trans (atlas_count_polynomial_bound hk.1 hk.2.1 hA hk.2.2.1 hk.2.2.2
    hC hCN hε₀ hε)

end Submission.Lib.K4FinitePlankAtlases
