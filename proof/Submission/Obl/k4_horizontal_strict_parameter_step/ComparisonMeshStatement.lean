import Mathlib

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Filter

/-- Uniformly resolving the finest mixed scale suffices for the actual native
comparison factory, before any old/native pair is selected. -/
def UniformComparisonMesh : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop →
    (∀ k, 1 ≤ K k) →
    (∀ a : ℝ, 0 < a → ∀ᶠ k in atTop, K k ≤ N k ^ a) →
    ∀ sMax e₀ R : ℝ, 0 < sMax → 100 * sMax ≤ e₀ → 100 * sMax ≤ R →
      ∀ᶠ k in atTop, ∀ s u ε E : ℝ,
        0 ≤ s → s ≤ sMax → 0 ≤ u → u ≤ 1 →
        0 ≤ ε → ε ≤ sMax → 0 ≤ E → E ≤ sMax →
        (200 * (N k ^ ε + 8 * K k ^ 4 * (1 + 6 * K k)) / N k ^ (-u * s)) *
          (N k ^ (-e₀) + K k * N k ^ (-R)) ≤ N k ^ (-s) * N k ^ (-E)

end Submission.Obl.k4_horizontal_strict_parameter_step
