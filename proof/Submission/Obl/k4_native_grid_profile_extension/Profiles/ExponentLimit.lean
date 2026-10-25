/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Profiles/ExponentLimit.lean. Earlier source attributions are retained below.
-/

import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity

/-!
# Typical exponents under subsequences and limits
-/

namespace Submission.Obl.k4_native_grid_profile_extension.Profiles

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Power-small bounds pass to every cofinal subsequence. -/
theorem IsPowerSmall.comp {N : ℕ → ℝ} {a : ℕ → ℝ≥0∞}
    (ha : IsPowerSmall N a) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    IsPowerSmall (N ∘ φ) (a ∘ φ) := by
  obtain ⟨c, hc, hbound⟩ := ha
  exact ⟨c, hc, hφ.eventually hbound⟩

/-- A convergent sequence of typical density exponents has its limit as a
fixed typical exponent. -/
theorem hasTypicalDensity_of_exponent_tendsto {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (μ : (k : ℕ) → Measure (α k)) (d : (k : ℕ) → α k → ℝ≥0∞)
    (e : ℕ → ℝ) (g : ℝ) (he : Tendsto e atTop (𝓝 g))
    (htypical : ∀ τ : ℝ, 0 < τ → IsPowerSmall N (fun k =>
      μ k {x | d k x < ENNReal.ofReal (N k ^ (-e k - τ)) ∨
        ENNReal.ofReal (N k ^ (-e k + τ)) < d k x})) :
    HasTypicalDensity N μ d g := by
  intro τ hτ
  obtain ⟨c, hc, hmass⟩ := htypical (τ / 2) (by positivity)
  have hnear := (Metric.tendsto_nhds.mp he) (τ / 2) (by positivity)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmass, hnear] with k hmassk hneark
  rw [Real.dist_eq] at hneark
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hneark
  refine (measure_mono ?_).trans hmassk
  intro x hx
  rcases hx with hx | hx
  · apply Or.inl
    exact hx.trans_le (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)))
  · apply Or.inr
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith))) hx

end Submission.Obl.k4_native_grid_profile_extension.Profiles
