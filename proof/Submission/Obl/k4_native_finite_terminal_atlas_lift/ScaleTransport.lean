/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/ScaleTransport.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.NativeTests
import Submission.Obl.k4_crop_angular_finite_tail.Grid

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

/-- The canonical dyadic thicknesses have only the single binary carry. -/
theorem thickness_product_bounds {N r s : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    δ N (r + s) ≤ δ N r * δ N s ∧ δ N r * δ N s ≤ 2 * δ N (r + s) := by
  obtain ⟨d, hd, _, he⟩ :=
    Submission.Obl.k4_crop_angular_finite_tail.width_product hN hr hs
  change δ N r * δ N s = (2 : ℝ) ^ d * δ N (r + s) at he
  have hp : 0 < δ N (r + s) := by unfold δ; positivity
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl <;> simp only [pow_zero,
    pow_one, one_mul] at he <;> rw [he] <;> constructor <;> linarith

theorem thickness_le_one {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) : δ N r ≤ 1 := by
  change Submission.Obl.k4_profile_density_bounds.width N r ≤ 1
  rw [Submission.Obl.k4_crop_angular_finite_tail.width_height hN hr, zpow_neg, zpow_natCast]
  exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- Scalar bounds of a child native test transfer with one fixed factor of two
in the value bound and with its original derivative unit. -/
theorem native_scalar_bounds {a b c κ B z z₁ z₂ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hκ : 0 ≤ κ)
    (hcarry : c ≤ a * b) (hcarry' : a * b ≤ 2 * c)
    (hz : |z| ≤ κ * b) (hz₁ : |z₁| ≤ κ * (B / a))
    (hz₂ : |z₂| ≤ κ * (B / a) ^ 2 / b) :
    |a * z| ≤ 2 * κ * c ∧ |a * z₁| ≤ κ * B ∧ |a * z₂| ≤ κ * B ^ 2 / c := by
  simp only [abs_mul, abs_of_pos ha]
  refine ⟨?_, ?_, ?_⟩
  · calc
      a * |z| ≤ a * (κ * b) := mul_le_mul_of_nonneg_left hz ha.le
      _ = κ * (a * b) := by ring
      _ ≤ κ * (2 * c) := mul_le_mul_of_nonneg_left hcarry' hκ
      _ = _ := by ring
  · calc
      a * |z₁| ≤ a * (κ * (B / a)) := mul_le_mul_of_nonneg_left hz₁ ha.le
      _ = _ := by field_simp <;> ring
  · calc
      a * |z₂| ≤ a * (κ * (B / a) ^ 2 / b) := mul_le_mul_of_nonneg_left hz₂ ha.le
      _ = κ * B ^ 2 / (a * b) := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hκ (sq_nonneg B)) hc hcarry

theorem native_scalar_floor {a κ B z : ℝ} (ha : 0 < a) (hfloor : (B / a) / κ ≤ |z|) :
    B / κ ≤ |a * z| := by
  rw [abs_mul, abs_of_pos ha]
  have h := mul_le_mul_of_nonneg_left hfloor ha.le
  convert h using 1 <;> field_simp <;> ring

end Submission.Obl.k4_native_finite_terminal_atlas_lift
