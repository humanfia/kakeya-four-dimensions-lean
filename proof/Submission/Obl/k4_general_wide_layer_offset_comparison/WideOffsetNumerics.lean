import Submission.Obl.k4_general_wide_layer_offset_comparison.WholeFiberOffsets
import Submission.Obl.k4_general_wide_layer_offset_comparison.WideFiberDiameter

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/WideOffsetNumerics.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Filter

noncomputable section

/-- Every actual long-domain width pair eventually places the whole
physical H-sized fiber in the matching half ball. -/
theorem eventually_wide_fiber_small {N H K : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k) (hK : ∀ k, 0 ≤ K k) (hKH : ∀ k, K k ≤ H k)
    (hHs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    {κ ℓ r u : ℝ} (hgap : ℓ * u < κ * r) :
    ∀ᶠ k in atTop, ∀ q βmin βmax : ℝ,
      0 ≤ q → q ≤ K k * N k ^ (-κ * r) →
      N k ^ (-ℓ * (r + u)) / H k ≤ βmin →
      βmax ≤ H k * N k ^ (-ℓ * r) →
      H k ^ 2 * (q * N k ^ (-ℓ * r) / βmin + q * βmax / βmin) ≤ 1 / 4 := by
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [hN k] : ∀ k, 1 ≤ N k) hNt hH hHs 5
    (show -κ * r + ℓ * u < 0 by linarith) (by norm_num : (0 : ℝ) ≤ 8)
  filter_upwards [hsmall] with k hk
  intro q βmin βmax hq hqu hβlo hβhi
  have hratio := wide_domain_ratio (by linarith [hN k] : 0 < N k)
    (hH k) (hK k) (hKH k) hq hqu hβlo hβhi
  simp only [Real.rpow_zero] at hk
  calc
    _ ≤ H k ^ 2 * (2 * H k ^ 3 * N k ^ (-κ * r + ℓ * u)) :=
      mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
    _ = 2 * H k ^ 5 * N k ^ (-κ * r + ℓ * u) := by ring
    _ ≤ _ := by linarith

/-- The long comparison threshold and the whole-fiber diameter give the
required fine offset error. The fixed margin absorbs the absolute Lipschitz
constant and every intrinsic subpower factor. -/
theorem eventually_wide_offset_error {N H K : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k) (hK : ∀ k, 0 ≤ K k) (hKH : ∀ k, K k ≤ H k)
    (hHs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    {κ ℓ r u C : ℝ} (hgap : (C + 1 + ℓ) * u < κ * r) :
    ∀ᶠ k in atTop, ∀ q βmin βmax : ℝ,
      0 ≤ q → q ≤ K k * N k ^ (-κ * r) →
      N k ^ (-ℓ * (r + u)) / H k ≤ βmin →
      βmax ≤ H k * N k ^ (-ℓ * r) →
      offsetLipschitz * (4 * H k * N k ^ (-r) * N k ^ (C * u)) *
        (H k ^ 2 * (q * N k ^ (-ℓ * r) / βmin + q * βmax / βmin)) ≤ N k ^ (-r - u) := by
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [hN k] : ∀ k, 1 ≤ N k) hNt hH hHs 6
    (show -r + C * u - κ * r + ℓ * u < -r - u by nlinarith)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) offsetLipschitz_pos.le)
  filter_upwards [hsmall] with k hk
  intro q βmin βmax hq hqu hβlo hβhi
  have hNp : 0 < N k := by linarith [hN k]
  have hH0 : 0 ≤ H k := zero_le_one.trans (hH k)
  have hratio := wide_domain_ratio hNp (hH k) (hK k) (hKH k) hq hqu hβlo hβhi
  have hpowers : N k ^ (-r) * N k ^ (C * u) * N k ^ (-κ * r + ℓ * u) =
      N k ^ (-r + C * u - κ * r + ℓ * u) := by
    rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]
    congr 1
    ring
  calc
    _ ≤ offsetLipschitz * (4 * H k * N k ^ (-r) * N k ^ (C * u)) *
        (H k ^ 2 * (2 * H k ^ 3 * N k ^ (-κ * r + ℓ * u))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hratio (sq_nonneg _))
        (mul_nonneg offsetLipschitz_pos.le (by positivity))
    _ = (8 * offsetLipschitz) * H k ^ 6 * N k ^ (-r + C * u - κ * r + ℓ * u) := by
      rw [show offsetLipschitz * (4 * H k * N k ^ (-r) * N k ^ (C * u)) *
          (H k ^ 2 * (2 * H k ^ 3 * N k ^ (-κ * r + ℓ * u))) =
          (8 * offsetLipschitz) * H k ^ 6 *
          (N k ^ (-r) * N k ^ (C * u) * N k ^ (-κ * r + ℓ * u)) by ring, hpowers]
    _ ≤ _ := hk.le

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
