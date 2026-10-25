import Submission.Obl.k4_general_wide_layer_offset_comparison.WideScales
import Submission.Obl.k4_profile_density_bounds.Asymptotics

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/WideFiberDiameter.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Filter

noncomputable section

/-- The strict wide-scale margin absorbs the diameter of the entire
physical H-sized fiber, uniformly over the actual long-domain widths. -/
theorem eventually_wide_fiber_diameter {N H K : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k) (hK : ∀ k, 0 ≤ K k) (hKH : ∀ k, K k ≤ H k)
    (hHs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    {κ ℓ r u C : ℝ}
    (hgap : (C + 3 + ℓ) * u < κ * r) :
    ∀ᶠ k in atTop, ∀ q βmin βmax : ℝ,
      0 ≤ q → q ≤ K k * N k ^ (-κ * r) →
      N k ^ (-ℓ * (r + u)) / H k ≤ βmin →
      βmax ≤ H k * N k ^ (-ℓ * r) →
      H k ^ 2 * (q * N k ^ (-ℓ * r) / βmin + q * βmax / βmin) ≤
        N k ^ (-(C + 3) * u) := by
  have hN1 : ∀ k, 1 ≤ N k := fun k => by linarith [hN k]
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hNt hH hHs 5
    (show -κ * r + ℓ * u < -(C + 3) * u by nlinarith) (by norm_num : (0 : ℝ) ≤ 2)
  filter_upwards [hsmall] with k hk
  intro q βmin βmax hq hqu hβlo hβhi
  have hratio := wide_domain_ratio (by linarith [hN k] : 0 < N k)
    (hH k) (hK k) (hKH k) hq hqu hβlo hβhi
  calc
    _ ≤ H k ^ 2 * (2 * H k ^ 3 * N k ^ (-κ * r + ℓ * u)) :=
      mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
    _ = 2 * H k ^ 5 * N k ^ (-κ * r + ℓ * u) := by ring
    _ ≤ _ := hk.le

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
