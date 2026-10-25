import Mathlib

set_option autoImplicit false

/-!
# Interfaces of the pieces of o273

The proof of `Submission.k4_conditional_common_affine_field` (paper, Section 8, "A common
coefficient field") is split into pieces with the precise statements below, so that they can be
proved independently.  The main file proves the theorem from these.

* `TwoDirectionSelection`: two separated velocity bins such that dense state mass has a witness
  in both (conditional palette domination and the palette ball cap).
* `LineMixedTerm`: one line of dense retained duration and Remez bound the mixed coefficient of a
  bilinear fit along a third direction.
-/

namespace Submission.Obl.k4_conditional_common_affine_field

/-- Two velocity bins `j₁, j₂` at distance at least `G` such that the states with positive mass in
both bins carry at least `1/(2K²)` of the total weight.  Here `m σ j` is the mass of state `σ` in
velocity bin `j`, `π j` the palette weight of bin `j`. -/
def TwoDirectionSelection : Prop :=
  ∀ {St : Type} (S : Finset St) (V : Finset ℤ) (w : St → ℝ) (m : St → ℤ → ℝ) (π : ℤ → ℝ)
    (K ε₀ : ℝ) (G : ℤ),
    0 < K → K * ε₀ ≤ 1 / 2 →
    (∀ σ ∈ S, ∀ j ∈ V, 0 ≤ m σ j) → (∀ j ∈ V, 0 ≤ π j) → ∑ j ∈ V, π j ≤ 1 →
    (∀ σ ∈ S, ∑ j ∈ V, m σ j = w σ) →
    (∀ σ ∈ S, ∀ j ∈ V, m σ j ≤ K * w σ * π j) →
    (∀ j ∈ V, ∑ j' ∈ V.filter (fun j' => |j - j'| < G), π j' ≤ ε₀) →
    0 < ∑ σ ∈ S, w σ →
    ∃ j₁ ∈ V, ∃ j₂ ∈ V, G ≤ |j₁ - j₂| ∧
      (∑ σ ∈ S, w σ) ≤ 2 * K ^ 2 * ∑ σ ∈ S.filter (fun σ => 0 < m σ j₁ ∧ 0 < m σ j₂), w σ

/-- Along the lines `t ↦ b l + t u l` of a law `μ ≤ K (ν ⊗ dt)`, a value `g` that is within `E₁`
of a bilinear function `β₀ + β₁ X₁ + β₂ X₂ + β₃ X₁ X₂` of the two axis intercepts
`X_k = b + t (u - w_k)` and within `E₂` of one of at most `n` affine functions of time of the line's
chart, on a set `E` of mass at least `m` whose velocities stay `r` away from both axes, has a small
mixed coefficient `β₃`. -/
def LineMixedTerm : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (ν : MeasureTheory.Measure α)
    (μ : MeasureTheory.Measure (α × ℝ)) {ι : Type} (chart : α → ι) (L : ι → Finset (Fin 3 → ℝ))
    (b u : α → ℝ) (g : α × ℝ → ℝ) (E : Set (α × ℝ)) (β : Fin 4 → ℝ)
    (K n m r E₁ E₂ w₁ w₂ : ℝ),
    MeasureTheory.IsProbabilityMeasure ν → 0 < K → 1 ≤ n → 0 < m → 0 < r →
    μ ≤ ENNReal.ofReal K • ν.prod MeasureTheory.volume →
    MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 → ENNReal.ofReal m ≤ μ E →
    (∀ i, ((L i).card : ℝ) ≤ n) →
    (∀ p ∈ E, |g p - (β 0 + β 1 * (b p.1 + p.2 * (u p.1 - w₁)) + β 2 * (b p.1 + p.2 * (u p.1 - w₂))
      + β 3 * (b p.1 + p.2 * (u p.1 - w₁)) * (b p.1 + p.2 * (u p.1 - w₂)))| ≤ E₁) →
    (∀ p ∈ E, ∃ a ∈ L (chart p.1), |g p - a 0 - a 1 * p.2| ≤ E₂) →
    (∀ p ∈ E, r ≤ |u p.1 - w₁| ∧ r ≤ |u p.1 - w₂|) →
    |β 3| * r ^ 2 ≤ 8 * (48 * K * n / m) ^ 2 * (E₁ + E₂)

end Submission.Obl.k4_conditional_common_affine_field
