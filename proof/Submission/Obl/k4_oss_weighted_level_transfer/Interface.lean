import Mathlib

/-!
# The finite weighted transfer (interface between the two halves of o043)

`FiniteTransfer s γ` is what remains of o043 once the probability law `α` has
been rounded to the grid `δ ℤ`: a finite `δ`-separated set `S` of cell corners
with cell masses `p`, and the projected collision sum with window `7 δ`.

* `finite_transfer_of_gain` (finite half): the frozen finite-gain hypothesis
  of o043 implies `FiniteTransfer s γ`.
* `conclusion_of_finiteTransfer` (discretization half): `FiniteTransfer s γ`
  implies the frozen conclusion of o043.
-/

open MeasureTheory

namespace Submission.Obl.k4_oss_weighted_level_transfer

/-- The weighted projected collision sum of a finite weighted set at slope `t`
with window `7 δ`. -/
noncomputable def collisionSum (S : Finset ℝ) (p : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  ∑ x₁ ∈ S, ∑ x₂ ∈ S, ∑ x₃ ∈ S, ∑ x₄ ∈ S,
    p x₁ * p x₂ * p x₃ * p x₄ *
      (if |(x₁ - x₂) - 2 * t * (x₃ - x₄)| ≤ 7 * δ then (1 : ℝ) else 0)

/-- The finite weighted transfer. -/
def FiniteTransfer (s γ : ℝ) : Prop :=
  ∃ c ε r : ℝ, 0 < c ∧ 0 < ε ∧ 0 < r ∧ r ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
    ∀ (S : Finset ℝ) (p : ℝ → ℝ) (Q : ℝ),
      (∀ x, 0 ≤ p x) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) →
      (∀ x ∈ S, |x| ≤ 2) →
      (S.card : ℝ) ≤ 4 / δ →
      ∑ x ∈ S, p x ≤ 1 →
      (∀ z u : ℝ, δ ≤ u → u ≤ 1 →
        ∑ x ∈ S.filter (fun x => dist x z ≤ u), p x ≤ 2 * δ ^ (-ε) * u ^ s) →
      ∑ x ∈ S, p x ^ 2 ≤ Q →
      δ ^ (1 - γ) ≤ Q →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 →
      (∀ x u : ℝ, δ ≤ u → u ≤ 1 →
        ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (4 * δ ^ (-ε) * u ^ s)) →
      ∫⁻ t, ENNReal.ofReal (collisionSum S p δ t) ∂ν ≤ ENNReal.ofReal (δ ^ c * Q)

end Submission.Obl.k4_oss_weighted_level_transfer
