import Mathlib
/- Adapted from this LOT tree, o077, x0250, GrowthBounds.lean at 6b0e9a0. -/
namespace Submission.Obl.k4_dyadic_crop_affine_laws
/-- An upper logarithmic growth exponent. -/
def HasUpperExponent (N A : ℕ → ℝ) (q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, A k ≤ N k ^ (q + ε)
end Submission.Obl.k4_dyadic_crop_affine_laws
