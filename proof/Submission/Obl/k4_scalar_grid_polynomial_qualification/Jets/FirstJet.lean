import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Determined
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.JetAlgebra
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Dyadic

set_option autoImplicit false

/-!
# The first jet (paper Prop. `prop:scalar-normal`, deterministic form, `j = 1`)

`FirstJetStatement`: for fixed `d < 1`, finitely many hierarchy exponents `γ i > 0` (dyadic
lengths `≈ N^{-γ i}`) and a finest exponent `γ₀ ≥ γ i`, `γ₀ > 0`, there is a floor exponent `cζ` such that
for every loss `ε > 0`, for `N` large and constants `K ≤ N^α`, every scalar-normal world with
floor `ζ ≤ N^{-cζ}` and every choice of dyadic levels `Tl i ≤ T₀` of those lengths admits

* a retained measurable label set `E₁ ⊆ E` of mass `≥ N^{-ε}`,
* a measurable time-only row `A`, bounded by `N^ε` at retained times,
* the Taylor estimate `|F v - F u - (v - u) A u| ≤ N^ε (2^{-Tl i})^{11/10}` for retained `u, v`
  in a common dyadic cell of level `Tl i`,
* the fine cover of the first jet `J₁ = x' - F(t) y' - A(t) y`: at every time `t`, on the
  trajectories retained at `t`, `J₁` lies within `N^ε (2^{-T₀})^{(1-d)/32}` of one of at most
  `N^ε` reals prescribed by the `2^{-T₀}`-bin of the scalar `S(t)`.

This is the paper's first-jet proposition with its entropy statement replaced by the
deterministic interval cover from which the paper derives it (slope concentration).
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open MeasureTheory Set

noncomputable section

/-- The rows at a leaf of the jet tree: `F t`, `A t`, then zeros. -/
def leafRows (F A : ℝ → ℝ) (t : ℝ) : ℕ → ℝ := fun i => if i = 0 then F t else if i = 1 then A t else 0

/-- **The first-jet statement.** -/
def FirstJetStatement : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ (r : ℕ) (γ : Fin r → ℝ) (γ₀ : ℝ), (∀ i, 0 < γ i) →
    (∀ i, γ i ≤ γ₀) → 0 < γ₀ →
    ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 5 → ℝ) (E : Set (Λ × ℝ))
        (F : ℝ → ℝ) (piece : ℝ → Λ → Fin 5 → ℤ) (K ζ : ℝ) (Tl : Fin r → ℕ) (T₀ : ℕ),
        K ≤ N ^ α → ζ ≤ N ^ (-cζ) →
        (∀ i, N ^ (-γ i) / K ≤ ((2 : ℝ) ^ Tl i)⁻¹ ∧ ((2 : ℝ) ^ Tl i)⁻¹ ≤ K * N ^ (-γ i)) →
        N ^ (-γ₀) / K ≤ ((2 : ℝ) ^ T₀)⁻¹ → ((2 : ℝ) ^ T₀)⁻¹ ≤ K * N ^ (-γ₀) →
        (∀ i, Tl i ≤ T₀) → ScalarNormal ν c E F piece K ζ d →
        ∃ E₁ : Set (Λ × ℝ), E₁ ⊆ E ∧ MeasurableSet E₁ ∧
          ENNReal.ofReal (N ^ (-ε)) ≤ (ν.prod volume) E₁ ∧
          ∃ A : ℝ → ℝ, Measurable A ∧ (∀ p ∈ E₁, |A p.2| ≤ N ^ ε) ∧
            (∀ i (j : ℤ), ∀ p ∈ E₁, ∀ p' ∈ E₁, p.2 ∈ dI (Tl i) j → p'.2 ∈ dI (Tl i) j →
              |F p'.2 - F p.2 - (p'.2 - p.2) * A p.2| ≤
                N ^ ε * (((2 : ℝ) ^ Tl i)⁻¹) ^ ((11 : ℝ) / 10)) ∧
            ∀ t : ℝ, Determined E₁ (fun l => zS F (c l) t) univ t ((2 : ℝ) ^ T₀)⁻¹
              (fun l => jet (leafRows F A t) (c l) t 1)
              (N ^ ε * (((2 : ℝ) ^ T₀)⁻¹) ^ ((1 - d) / 32)) ⌊N ^ ε⌋₊

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
