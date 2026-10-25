-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.SmallLength.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

/-- The failure-length regime bounds the largest balanced fine fibre. -/
theorem maximum_fibre_regime {δ ρ θ ζ D : ℝ} {n N : ℕ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hn : 0 < n) (hD : 0 ≤ D)
    (hsize : (N : ℝ) * D ≤ δ ^ (-θ) * n)
    (hregime : δ / ρ ≤ δ ^ ζ * (ρ / δ) * N / n) :
    D * δ ^ 2 ≤ δ ^ (ζ - θ) * ρ ^ 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hr : δ ^ 2 * n ≤ δ ^ ζ * ρ ^ 2 * N := by
    have hh := (le_div_iff₀ hn').mp hregime
    have hh' := mul_le_mul_of_nonneg_right hh (mul_pos hρ hδ).le
    convert hh' using 1 <;> field_simp <;> ring
  apply (mul_le_mul_iff_of_pos_right hn').mp
  calc
    D * δ ^ 2 * n = (δ ^ 2 * n) * D := by ring
    _ ≤ (δ ^ ζ * ρ ^ 2 * N) * D := mul_le_mul_of_nonneg_right hr hD
    _ = (δ ^ ζ * ρ ^ 2) * (N * D) := by ring
    _ ≤ (δ ^ ζ * ρ ^ 2) * (δ ^ (-θ) * n) :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = δ ^ (ζ - θ) * ρ ^ 2 * n := by
      rw [show ζ - θ = ζ + (-θ) by ring, Real.rpow_add hδ]
      ring

/-- A single length works for all fine fibres when the coarse radius is
doubled. The upper range is set by the largest fibre. -/
theorem small_radius_prescribed_length {δ ρ θ ζ ε e D : ℝ} {n N : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hn : 0 < n) (hD : 0 < D)
    (hsize : (N : ℝ) * D ≤ δ ^ (-θ) * n)
    (hregime : δ / ρ ≤ δ ^ ζ * (ρ / δ) * N / n)
    (hbudget : e + θ ≤ ζ / 2) (herror : e + θ ≤ ε) :
    δ ^ (1 - ζ / 2) / (2 * ρ) ≤ δ ^ e * (2 * ρ / δ) / D ∧
      δ ^ ε * (ρ / δ) * N / n ≤ δ ^ e * (2 * ρ / δ) / D := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmax := maximum_fibre_regime hδ hρ hn hD.le hsize hregime
  have hpow : δ ^ (ζ - θ - ζ / 2) ≤ δ ^ e :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hscale : D * δ ^ (2 - ζ / 2) ≤ δ ^ e * ρ ^ 2 := by
    calc
      _ = (D * δ ^ 2) * δ ^ (-ζ / 2) := by
        rw [show (2 - ζ / 2 : ℝ) = 2 + (-ζ / 2) by ring, Real.rpow_add hδ,
          Real.rpow_two]
        ring
      _ ≤ (δ ^ (ζ - θ) * ρ ^ 2) * δ ^ (-ζ / 2) :=
        mul_le_mul_of_nonneg_right hmax (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (ζ - θ - ζ / 2) * ρ ^ 2 := by
        rw [show ζ - θ - ζ / 2 = (ζ - θ) + (-ζ / 2) by ring, Real.rpow_add hδ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow (sq_nonneg ρ)
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 2 * ρ) hD]
    apply (mul_le_mul_iff_of_pos_right hδ).mp
    calc
      (δ ^ (1 - ζ / 2) * D) * δ = D * δ ^ (2 - ζ / 2) := by
        have he : δ ^ (1 - ζ / 2) * δ = δ ^ (2 - ζ / 2) := by
          calc
            _ = δ ^ (1 - ζ / 2) * δ ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
        calc
          _ = D * (δ ^ (1 - ζ / 2) * δ) := by ring
          _ = _ := by rw [he]
      _ ≤ δ ^ e * ρ ^ 2 := hscale
      _ ≤ 4 * (δ ^ e * ρ ^ 2) := by nlinarith [show 0 ≤ δ ^ e * ρ ^ 2 by positivity]
      _ = (δ ^ e * (2 * ρ / δ) * (2 * ρ)) * δ := by field_simp; ring
  · rw [div_le_div_iff₀ hn' hD]
    have hp : δ ^ (ε - θ) ≤ δ ^ e :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    calc
      (δ ^ ε * (ρ / δ) * N) * D = (δ ^ ε * (ρ / δ)) * (N * D) := by ring
      _ ≤ (δ ^ ε * (ρ / δ)) * (δ ^ (-θ) * n) :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = δ ^ (ε - θ) * (ρ / δ) * n := by
        rw [show ε - θ = ε + (-θ) by ring, Real.rpow_add hδ]
        ring
      _ ≤ δ ^ e * (ρ / δ) * n := by gcongr
      _ ≤ δ ^ e * (2 * ρ / δ) * n := by gcongr; linarith

end WangZahlLot.Obl.wz_coarse_grains_assembly
