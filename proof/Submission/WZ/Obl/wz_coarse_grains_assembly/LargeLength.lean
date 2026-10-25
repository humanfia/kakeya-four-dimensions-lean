-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.LargeLength.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.PowerBudget

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

/-- In the length-growth regime, a bounded coarse count allows the common
length `δ^(ε/2)/(δ n)`. It exceeds both the requested output length and the
minimum length of the single-tube construction. -/
theorem large_radius_prescribed_length {δ ρ ε ζ θ : ℝ} {n N : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hn : 0 < n)
    (hN : (N : ℝ) ≤ δ ^ (-θ)) (hθε : θ ≤ ε / 2) (hbudget : θ + ε / 2 ≤ ζ / 2)
    (hreg : δ / ρ ≤ δ ^ ζ * (ρ / δ) * N / n) :
    δ ^ (1 - ζ / 2) ≤ δ ^ (ε / 2) / (δ * n) ∧
      δ ^ ε * (ρ / δ) * N / n ≤ δ ^ (ε / 2) / (δ * n) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hden : 0 < ρ * δ * n := by positivity
  have hreg' : δ ^ 2 * n ≤ δ ^ ζ * ρ ^ 2 * N := by
    have hh := mul_le_mul_of_nonneg_right hreg hden.le
    have hl : δ / ρ * (ρ * δ * n) = δ ^ 2 * n := by field_simp
    have hr : (δ ^ ζ * (ρ / δ) * N / n) * (ρ * δ * n) = δ ^ ζ * ρ ^ 2 * N := by
      field_simp
    rwa [hl, hr] at hh
  have hnup : δ ^ 2 * n ≤ δ ^ (ζ - θ) := by
    calc
      _ ≤ δ ^ ζ * ρ ^ 2 * N := hreg'
      _ ≤ δ ^ ζ * 1 * N := by gcongr; nlinarith
      _ = (N : ℝ) * δ ^ ζ := by ring
      _ ≤ δ ^ (ζ - θ) := rpow_absorb hδ hδ1 hN (by linarith)
  have hdn : 0 < δ * (n : ℝ) := mul_pos hδ hnR
  constructor
  · apply (le_div_iff₀ hdn).mpr
    calc
      δ ^ (1 - ζ / 2) * (δ * n) = δ ^ (-ζ / 2) * (δ ^ 2 * n) := by
        rw [show 1 - ζ / 2 = -ζ / 2 + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
        ring
      _ ≤ δ ^ (-ζ / 2) * δ ^ (ζ - θ) := by gcongr
      _ = δ ^ (ζ / 2 - θ) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  · have he : δ ^ ε * (ρ / δ) * N / n = ρ * ((N : ℝ) * δ ^ ε) / (δ * n) := by
      ring
    rw [he]
    apply (div_le_div_iff_of_pos_right hdn).mpr
    calc
      ρ * ((N : ℝ) * δ ^ ε) ≤ 1 * ((N : ℝ) * δ ^ ε) := by gcongr
      _ = (N : ℝ) * δ ^ ε := one_mul _
      _ ≤ δ ^ (ε / 2) := rpow_absorb hδ hδ1 hN (by linarith)

/-- Replacing the full family size by a smaller retained size only raises
the permissible upper length, even after reserving exponent slack. -/
theorem prescribed_length_le_single_tube {δ ε e : ℝ} {n s : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 < s) (hsn : s ≤ n) (he : e ≤ ε / 2) :
    δ ^ (ε / 2) / (δ * n) ≤ δ ^ e * (1 / δ) / s := by
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hnR : (0 : ℝ) < n := hsR.trans_le (Nat.cast_le.mpr hsn)
  calc
    _ ≤ δ ^ e / (δ * n) :=
      (div_le_div_iff_of_pos_right (mul_pos hδ hnR)).mpr
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 he)
    _ ≤ δ ^ e / (δ * s) := div_le_div_of_nonneg_left (Real.rpow_nonneg hδ.le _)
      (mul_pos hδ hsR) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hsn) hδ.le)
    _ = _ := by ring

end WangZahlLot.Obl.wz_coarse_grains_assembly
