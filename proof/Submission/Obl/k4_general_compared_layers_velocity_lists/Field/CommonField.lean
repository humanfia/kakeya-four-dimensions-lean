-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.CommonField; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Mathlib

/-!
# The common affine field principle (frozen statement of o273)

`CommonFieldPrinciple` is, verbatim, the frozen statement of the open obligation
o273 `k4_conditional_common_affine_field` (child of o250, opened 2026-10-21T15:25Z):
a dense line-time law with a fine two-dimensional base ceiling, a non-concentrated
velocity palette dominated conditionally on the actual fine position/coefficient
state, and subpower chart lists of affine/constant coefficient pairs, agrees on
dense mass with one affine first coefficient and one constant second coefficient.
It is used here only as an explicit hypothesis, for the common transverse field of
the wide-interval argument (paper Prop. 8.4).
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

/-- The frozen statement of o273, as a proposition. -/
def CommonFieldPrinciple : Prop :=
  ∀ S : ℝ, 0 < S → ∃ C₀ : ℝ, 100 < C₀ ∧ ∀ A θ : ℝ, 0 < A → 0 < θ → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (π : MeasureTheory.Measure ℝ) (b v : α → ℝ) (v₀ χb χv : ℝ) (f : α × ℝ → Fin 2 → ℝ) (L : (ℤ × ℤ) → Finset (Fin 3 → ℝ)), (fun (δ e : ℝ) => (fun (z : α × ℝ → Fin 2 → ℝ) => (fun (state : α × ℝ → Fin 4 → ℤ) => Measurable b → Measurable v → Measurable f → MeasureTheory.IsProbabilityMeasure ν → MeasureTheory.IsProbabilityMeasure π → N ^ (-A) ≤ χb → χb ≤ 1 → N ^ (-A) ≤ χv → χv ≤ 1 → (∀ l, |b l| + |v l| + |v₀| ≤ N ^ η) → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ᵐ p ∂μ, ∀ i, |f p i| ≤ N ^ η) → (∀ q : Fin 2 → ℤ, μ {p | (fun i => ⌊z p i / δ⌋) = q} ≤ ENNReal.ofReal (N ^ η * δ ^ 2)) → (∀ x r : ℝ, δ ≤ r → r ≤ 1 → π (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) → (∀ (q : Fin 4 → ℤ) (j : ℤ), μ {p | state p = q ∧ ⌊v p.1 / δ⌋ = j} ≤ ENNReal.ofReal (N ^ η) * μ {p | state p = q} * π (Set.Ico ((j : ℝ) * δ) (((j : ℝ) + 1) * δ))) → (∀ q, ((L q).card : ℝ) ≤ N ^ η) → (∀ q, ∀ a ∈ L q, ∀ i, |a i| ≤ N ^ η) → (∀ᵐ p ∂μ, ∃ a ∈ L (⌊b p.1 / χb⌋, ⌊v p.1 / χv⌋), |f p 0 - a 0 - a 1 * p.2| ≤ N ^ η * e ∧ |f p 1 - a 2| ≤ N ^ η * e) → ∃ C : Fin 4 → ℝ, (∀ i, |C i| ≤ N ^ ε) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | |f p 0 - C 0 - C 1 * z p 0 - C 2 * z p 1| ≤ N ^ ε * e ∧ |f p 1 - C 3| ≤ N ^ ε * e}) (fun p => ![⌊z p 0 / δ⌋, ⌊z p 1 / δ⌋, ⌊f p 0 / e⌋, ⌊f p 1 / e⌋])) (fun p => ![p.2, b p.1 + p.2 * (v p.1 - v₀)])) (N ^ (-(C₀ * (A + θ)))) (N ^ (-θ))

end Submission.Obl.k4_general_compared_layers_velocity_lists
