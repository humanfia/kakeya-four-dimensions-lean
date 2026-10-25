-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Mathlib

namespace Submission.Obl.k4_finite_affine_parent_sources

/-- Relative profile errors cost twice the uniform affine error. -/
theorem flat_profile_difference (f : ℝ → ℝ) (d L error : ℝ)
    (hflat : ∀ q, 0 ≤ q → q ≤ L → |f q - f 0 - d * q| ≤ error * L)
    (b c : ℝ) (hb : 0 ≤ b) (hbL : b ≤ L) (hc : 0 ≤ c) (hcL : c ≤ L) :
    |f c - f b - d * (c - b)| ≤ 2 * error * L := by
  calc
    _ = |(f c - f 0 - d * c) - (f b - f 0 - d * b)| := by ring_nf
    _ ≤ |f c - f 0 - d * c| + |f b - f 0 - d * b| := abs_sub _ _
    _ ≤ error * L + error * L := add_le_add (hflat c hc hcL) (hflat b hb hbL)
    _ = _ := by ring

/-- A full-prior lower floor cancels the absolute density offset of its parent. -/
theorem parent_density_ratio_bound {N κ D A fb fc d b c error : ℝ}
    (hN : 1 ≤ N) (hκ : 0 < κ) (hA : 0 < A)
    (hfloor : N ^ (-fb) * D / κ ≤ A)
    (hprofile : d * (c - b) - error ≤ fc - fb) :
    (D / A) * N ^ (-fc) ≤ κ * N ^ (-d * (c - b) + error) := by
  have hN0 : 0 < N := by linarith
  have hcancel : N ^ fb * N ^ (-fb) = 1 := by
    rw [← Real.rpow_add hN0]
    simp
  have hf := (div_le_iff₀ hκ).mp hfloor
  have hratio : D / A ≤ κ * N ^ fb := by
    apply (div_le_iff₀ hA).mpr
    calc
      D = N ^ fb * (N ^ (-fb) * D) := by rw [← mul_assoc, hcancel, one_mul]
      _ ≤ N ^ fb * (A * κ) := mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hN0.le _)
      _ = _ := by ring
  calc
    _ ≤ (κ * N ^ fb) * N ^ (-fc) :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hN0.le _)
    _ = κ * N ^ (fb - fc) := by rw [mul_assoc, ← Real.rpow_add hN0]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hκ.le

end Submission.Obl.k4_finite_affine_parent_sources
