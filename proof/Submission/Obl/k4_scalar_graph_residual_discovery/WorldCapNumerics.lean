/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldCapNumerics.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Interpolation from the original preparation grid costs only a fixed
power of its scale ratio. This constant is used AFTER residual choice. -/
theorem interpolated_spatial_cap_constant {ρ β δ r a H A η d : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hδ : 0 < δ) (hr : 0 < r) (ha : 0 < a)
    (hH : 0 < H) (hA : 1 ≤ A) (hη : 0 < η) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    (hδle : δ ≤ ρ * a) (hδge : ρ * a ≤ A * δ) (hβge : ρ * r ≤ A * β) :
    ((ρ * a / δ + 2) ^ 2 * (H * δ ^ (1 + d))) /
        (η * (β ^ (1 + d) / H)) ≤
      (9 * H ^ 2 * A ^ 4 / η) * (a / r) ^ (1 + d) := by
  have hA₀ : 0 < A := by linarith
  have hp : 0 ≤ 1 + d := by linarith
  have hβpow : 0 < β ^ (1 + d) := Real.rpow_pos_of_pos hβ _
  have hcover : (ρ * a / δ + 2) ^ 2 ≤ 9 * A ^ 2 := by
    have hc : ρ * a / δ ≤ A := (div_le_iff₀ hδ).mpr hδge
    nlinarith [div_nonneg (mul_nonneg hρ.le ha.le) hδ.le]
  have hratio : δ / β ≤ A * (a / r) := by
    apply (div_le_iff₀ hβ).mpr
    have hh := mul_le_mul_of_nonneg_right hβge (div_nonneg ha.le hr.le)
    have heq : (ρ * r) * (a / r) = ρ * a := by field_simp
    rw [heq] at hh
    exact hδle.trans (by nlinarith only [hh])
  have hpower : (δ / β) ^ (1 + d) ≤ A ^ 2 * (a / r) ^ (1 + d) := by
    calc
      _ ≤ (A * (a / r)) ^ (1 + d) := Real.rpow_le_rpow (div_nonneg hδ.le hβ.le) hratio hp
      _ = A ^ (1 + d) * (a / r) ^ (1 + d) :=
        Real.mul_rpow hA₀.le (div_nonneg ha.le hr.le)
      _ ≤ A ^ (2 : ℝ) * (a / r) ^ (1 + d) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hA (by linarith : 1 + d ≤ (2 : ℝ)))
          (Real.rpow_nonneg (div_nonneg ha.le hr.le) _)
      _ = _ := by norm_num
  have hidentity :
      ((ρ * a / δ + 2) ^ 2 * (H * δ ^ (1 + d))) /
          (η * (β ^ (1 + d) / H)) =
        (H ^ 2 / η) * (ρ * a / δ + 2) ^ 2 * (δ / β) ^ (1 + d) := by
    rw [Real.div_rpow hδ.le hβ.le]
    field_simp
  rw [hidentity]
  calc
    _ ≤ (H ^ 2 / η) * (9 * A ^ 2) * (A ^ 2 * (a / r) ^ (1 + d)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcover (by positivity)) hpower
        (Real.rpow_nonneg (div_nonneg hδ.le hβ.le) _) (by positivity)
    _ = _ := by ring

/-- The same numerical estimate in the exact extended-real form output
by the original-palette cancellation. -/
theorem interpolated_spatial_cap_constant_ennreal {ρ β δ r a H A η d : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hδ : 0 < δ) (hr : 0 < r) (ha : 0 < a)
    (hH : 0 < H) (hA : 1 ≤ A) (hη : 0 < η) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    (hδle : δ ≤ ρ * a) (hδge : ρ * a ≤ A * δ) (hβge : ρ * r ≤ A * β) :
    (ENNReal.ofReal ((ρ * a / δ + 2) ^ 2) * ENNReal.ofReal (H * δ ^ (1 + d))) /
        (ENNReal.ofReal η * ENNReal.ofReal (β ^ (1 + d) / H)) ≤
      ENNReal.ofReal ((9 * H ^ 2 * A ^ 4 / η) * (a / r) ^ (1 + d)) := by
  have hβpow : 0 < β ^ (1 + d) := Real.rpow_pos_of_pos hβ _
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hη.le,
    ← ENNReal.ofReal_div_of_pos (mul_pos hη (div_pos hβpow hH))]
  exact ENNReal.ofReal_le_ofReal
    (interpolated_spatial_cap_constant hρ hβ hδ hr ha hH hA hη hd hd₁ hδle hδge hβge)

end

end Submission.Obl.k4_scalar_graph_residual_discovery
