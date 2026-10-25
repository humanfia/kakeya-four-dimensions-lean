-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.LightArithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

/-- The fixed coefficient in the cubic light-class estimate. -/
def lightMassConstant (q : ℝ) : ℝ := (6048 * q) ^ 3 * 6 ^ 3 * 9 * 432 * 26 ^ 3

/-- Quantitative absorption of the light-class coefficient. This separates real-power
bookkeeping from all measure and finite-family arguments. -/
theorem light_cubic_coefficient_bound {δ ρ τ ε s e v t q N : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hN : 0 ≤ N)
    (hlower : δ ≤ ρ * τ) (hupper : ρ * τ ≤ 26 * δ)
    (hscale : τ ≤ δ ^ (ε ^ 2 / 2))
    (hexp : ε / 2 ≤ 3 * s - 3 + ε - 2 * e)
    (hsmall : lightMassConstant q * δ ^ (ε ^ 3 / 4 - 3 * v - 3 * t) ≤ 1) :
    (6048 * q * δ ^ (-v) * τ ^ s * N) ^ 3 *
      ((6 * δ) ^ 3 * ρ ^ 2 * (9 * (δ / ρ) ^ ε * (432 * ρ)) * (τ ^ (-e)) ^ 2) ≤
        (δ ^ t * N * δ ^ 2) ^ 3 := by
  let E := 3 * s - 3 + ε - 2 * e
  let K := (6048 * q) ^ 3 * 6 ^ 3 * 9 * 432
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hratio : δ / ρ ≤ τ := (div_le_iff₀ hρ).mpr (by nlinarith)
  have hpow : (δ / ρ) ^ ε ≤ τ ^ ε := Real.rpow_le_rpow (by positivity) hratio hε
  have htau : τ ^ 3 * τ ^ E = (τ ^ s) ^ 3 * τ ^ ε * (τ ^ (-e)) ^ 2 := by
    rw [← Real.rpow_natCast τ 3, ← Real.rpow_mul_natCast hτ.le s 3,
      ← Real.rpow_mul_natCast hτ.le (-e) 2]
    simp only [← Real.rpow_add hτ]
    congr 1
    dsimp [E]
    ring
  have hgain : (δ ^ (-v)) ^ 3 * τ ^ E ≤ δ ^ (ε ^ 3 / 4 - 3 * v) := by
    calc
      _ ≤ (δ ^ (-v)) ^ 3 * τ ^ (ε / 2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hτ hτ1 hexp) (by positivity)
      _ ≤ (δ ^ (-v)) ^ 3 * (δ ^ (ε ^ 2 / 2)) ^ (ε / 2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hτ.le hscale (by positivity)) (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 1
        ring
  have hdelta : δ ^ (ε ^ 3 / 4 - 3 * v) =
      δ ^ (ε ^ 3 / 4 - 3 * v - 3 * t) * (δ ^ t) ^ 3 := by
    rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ ≤ (6048 * q * δ ^ (-v) * τ ^ s * N) ^ 3 *
        ((6 * δ) ^ 3 * ρ ^ 2 * (9 * τ ^ ε * (432 * ρ)) * (τ ^ (-e)) ^ 2) := by gcongr
    _ = K * N ^ 3 * δ ^ 3 * (δ ^ (-v)) ^ 3 * ρ ^ 3 *
        ((τ ^ s) ^ 3 * τ ^ ε * (τ ^ (-e)) ^ 2) := by dsimp [K]; ring
    _ = K * N ^ 3 * δ ^ 3 * (δ ^ (-v)) ^ 3 * (ρ * τ) ^ 3 * τ ^ E := by
      rw [← htau]
      ring
    _ ≤ K * N ^ 3 * δ ^ 3 * (δ ^ (-v)) ^ 3 * (26 * δ) ^ 3 * τ ^ E := by gcongr
    _ = lightMassConstant q * N ^ 3 * δ ^ 6 * ((δ ^ (-v)) ^ 3 * τ ^ E) := by
      dsimp [K, lightMassConstant]
      ring
    _ ≤ lightMassConstant q * N ^ 3 * δ ^ 6 * δ ^ (ε ^ 3 / 4 - 3 * v) :=
      mul_le_mul_of_nonneg_left hgain (by dsimp [lightMassConstant]; positivity)
    _ = (lightMassConstant q * δ ^ (ε ^ 3 / 4 - 3 * v - 3 * t)) *
        (δ ^ t * N * δ ^ 2) ^ 3 := by rw [hdelta]; ring
    _ ≤ 1 * (δ ^ t * N * δ ^ 2) ^ 3 := mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

/-- ENNReal form of the coefficient estimate, with the cubic root already taken. -/
theorem light_mass_of_cubic_bound {δ ρ τ ε s e v t q N : ℝ} {M : ENNReal}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hN : 0 ≤ N)
    (hlower : δ ≤ ρ * τ) (hupper : ρ * τ ≤ 26 * δ)
    (hscale : τ ≤ δ ^ (ε ^ 2 / 2))
    (hexp : ε / 2 ≤ 3 * s - 3 + ε - 2 * e)
    (hsmall : lightMassConstant q * δ ^ (ε ^ 3 / 4 - 3 * v - 3 * t) ≤ 1)
    (hm : M ^ 3 ≤ ENNReal.ofReal (6048 * q * δ ^ (-v) * τ ^ s * N) ^ 3 *
      (ENNReal.ofReal (6 * δ) ^ 3 * ENNReal.ofReal ρ ^ 2 *
        ((9 * ENNReal.ofReal ((δ / ρ) ^ ε)) * ENNReal.ofReal (432 * ρ)) *
          ENNReal.ofReal (τ ^ (-e)) ^ 2)) :
    M ≤ ENNReal.ofReal (δ ^ t * N * δ ^ 2) := by
  have hr := ENNReal.ofReal_le_ofReal
    (light_cubic_coefficient_bound hδ hρ hτ hτ1 hε hq hN hlower hupper hscale hexp hsmall)
  have he : ENNReal.ofReal
      ((6048 * q * δ ^ (-v) * τ ^ s * N) ^ 3 *
        ((6 * δ) ^ 3 * ρ ^ 2 * (9 * (δ / ρ) ^ ε * (432 * ρ)) * (τ ^ (-e)) ^ 2)) =
      ENNReal.ofReal (6048 * q * δ ^ (-v) * τ ^ s * N) ^ 3 *
        (ENNReal.ofReal (6 * δ) ^ 3 * ENNReal.ofReal ρ ^ 2 *
          ((9 * ENNReal.ofReal ((δ / ρ) ^ ε)) * ENNReal.ofReal (432 * ρ)) *
            ENNReal.ofReal (τ ^ (-e)) ^ 2) := by
    repeat first
      | rw [ENNReal.ofReal_mul (by positivity)]
      | rw [ENNReal.ofReal_pow (by positivity)]
    norm_num
  rw [he, ENNReal.ofReal_pow (by positivity)] at hr
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (3 : ℕ) ≠ 0)).mp (hm.trans hr)

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
