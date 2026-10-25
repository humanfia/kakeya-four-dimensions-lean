-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.Scalar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.Basic

namespace WangZahlLot.Obl.wz_separated_scales_gain

/-- The separated scales turn the difference of the two exponents into a power gain. -/
theorem separated_power_gain {δ τ ρ ζ g : ℝ} (hδ : 0 < δ) (hτ : 0 < τ)
    (hρ : 0 < ρ) (hsep : τ ≤ δ ^ ζ * ρ) (hg : 0 ≤ g) :
    δ ^ (-(ζ * g)) ≤ (ρ / τ) ^ g := by
  have hratio : (δ ^ ζ)⁻¹ ≤ ρ / τ := by
    apply (le_div_iff₀ hτ).mpr
    apply (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hδ ζ)).mpr
    simpa only [mul_comm] using hsep
  calc
    δ ^ (-(ζ * g)) = ((δ ^ ζ)⁻¹) ^ g := by
      rw [← Real.rpow_neg hδ.le, ← Real.rpow_mul hδ.le]
      congr 1
      ring
    _ ≤ (ρ / τ) ^ g := Real.rpow_le_rpow (by positivity) hratio hg

/-- Comparison of the gained product with the requested final exponent. -/
theorem separated_target_le_product {δ τ ρ ζ g ω' α ε e A N σ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hsep : τ ≤ δ ^ ζ * ρ) (hg : 0 ≤ g) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hloss : α + e ≤ ζ * g + ε) :
    A * δ ^ (ω' - α + ε) * N ^ (σ / 2) ≤
      A * δ ^ (ω' + e) * (ρ / τ) ^ g * N ^ (σ / 2) := by
  have hp := separated_power_gain hδ hτ hρ hsep hg
  have he : δ ^ (ω' - α + ε) ≤ δ ^ (ω' + e) * (ρ / τ) ^ g := by
    calc
      _ ≤ δ ^ (ω' + e - ζ * g) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ (ω' + e) * δ ^ (-(ζ * g)) := by
        rw [← Real.rpow_add hδ]
        congr 1
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hδ.le _)
  calc
    _ ≤ A * (δ ^ (ω' + e) * (ρ / τ) ^ g) * N ^ (σ / 2) := by gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_separated_scales_gain
