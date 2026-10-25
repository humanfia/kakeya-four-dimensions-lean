-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Scalar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- The nonflat alternative forces the larger width to be a power of the fine scale. -/
theorem coarse_width_bound {δ a b ζ β : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hβ : β ≤ ζ / 4)
    (hvol : a * b ≤ δ ^ (ζ / 2)) (hflat : δ ^ β * b < a) :
    b ≤ δ ^ (ζ / 8) := by
  have hpow := Real.rpow_pos_of_pos hδ β
  have hs : δ ^ β * b ^ 2 ≤ δ ^ (ζ / 2) := by
    calc
      δ ^ β * b ^ 2 = (δ ^ β * b) * b := by ring
      _ ≤ a * b := mul_le_mul_of_nonneg_right hflat.le hb
      _ ≤ δ ^ (ζ / 2) := hvol
  have hs' : b ^ 2 ≤ δ ^ (ζ / 2 - β) := by
    apply (mul_le_mul_iff_right₀ hpow).mp
    calc
      δ ^ β * b ^ 2 ≤ δ ^ (ζ / 2) := hs
      _ = δ ^ β * δ ^ (ζ / 2 - β) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
  have hs'' : b ^ 2 ≤ (δ ^ (ζ / 8)) ^ 2 := by
    calc
      b ^ 2 ≤ δ ^ (ζ / 2 - β) := hs'
      _ ≤ δ ^ (ζ / 4) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = (δ ^ (ζ / 8)) ^ 2 := by
        rw [← Real.rpow_natCast (δ ^ (ζ / 8)) 2, ← Real.rpow_mul hδ.le]
        congr 1
        norm_num
        ring
  nlinarith [Real.rpow_pos_of_pos hδ (ζ / 8)]

/-- Conversion of the two-scale scalar factor to a strict gain. -/
theorem two_scale_power_gain {δ b ζ ω u e : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 < b)
    (hbδ : b ≤ δ ^ (ζ / 8)) (hgap : ω < u)
    (hegap : e ≤ (u - ω) / 2) (hegain : e ≤ ζ * (u - ω) / 32)
    (hζ : 0 < ζ) :
    δ ^ (u - ζ * (u - ω) / 32) ≤ δ ^ (u + e) * b ^ (ω - u + e) := by
  have he : ω - u + e ≤ 0 := by linarith
  have hneg := Real.rpow_le_rpow_of_nonpos hb hbδ he
  have h₁ : δ ^ (u + e) * (δ ^ (ζ / 8)) ^ (ω - u + e) =
      δ ^ (u + e + (ζ / 8) * (ω - u + e)) := by
    rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
  have hexp : u + e + (ζ / 8) * (ω - u + e) ≤
      u - ζ * (u - ω) / 32 := by
    nlinarith [mul_nonneg hζ.le (sub_nonneg.mpr hegap)]
  calc
    δ ^ (u - ζ * (u - ω) / 32) ≤
        δ ^ (u + e + (ζ / 8) * (ω - u + e)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
    _ = δ ^ (u + e) * (δ ^ (ζ / 8)) ^ (ω - u + e) := h₁.symm
    _ ≤ δ ^ (u + e) * b ^ (ω - u + e) :=
      mul_le_mul_of_nonneg_left hneg (Real.rpow_nonneg hδ.le _)

end WangZahlLot.Obl.wz_nonflat_factored_improvement
