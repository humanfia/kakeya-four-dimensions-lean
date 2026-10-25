-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.FirstJet, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/FirstJet.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/FirstJet.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/FirstJet.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Determined
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.JetAlgebra
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Dyadic

set_option autoImplicit false

/-!
# The first jet (paper Prop. `prop:scalar-normal`, deterministic form, `j = 2`)

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `ec0250f0`,
`Jets/FirstJet.lean` (the `j = 1` statement; updated to `38917d30`), for rows in `(ℝ²)^*` (sup norms).
The paper states Prop. `prop:scalar-normal` for `j ∈ {1, 2}` with the same exponents.

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

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set

noncomputable section

/-- The rows at a leaf of the jet tree: `F t`, `A t`, then zeros. -/
def leafRows (F A : ℝ → Fin 2 → ℝ) (t : ℝ) : ℕ → Fin 2 → ℝ :=
  fun i => if i = 0 then F t else if i = 1 then A t else 0

/-- **The first-jet statement.** -/
def FirstJetStatement : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ (r : ℕ) (γ : Fin r → ℝ) (γ₀ : ℝ), (∀ i, 0 < γ i) →
    (∀ i, γ i ≤ γ₀) → 0 < γ₀ →
    ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
        (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Λ → Fin 7 → ℤ) (K ζ : ℝ) (Tl : Fin r → ℕ) (T₀ : ℕ),
        K ≤ N ^ α → ζ ≤ N ^ (-cζ) →
        (∀ i, N ^ (-γ i) / K ≤ ((2 : ℝ) ^ Tl i)⁻¹ ∧ ((2 : ℝ) ^ Tl i)⁻¹ ≤ K * N ^ (-γ i)) →
        N ^ (-γ₀) / K ≤ ((2 : ℝ) ^ T₀)⁻¹ → ((2 : ℝ) ^ T₀)⁻¹ ≤ K * N ^ (-γ₀) →
        (∀ i, Tl i ≤ T₀) → ScalarNormal ν c E F piece K ζ d →
        ∃ E₁ : Set (Λ × ℝ), E₁ ⊆ E ∧ MeasurableSet E₁ ∧
          ENNReal.ofReal (N ^ (-ε)) ≤ (ν.prod volume) E₁ ∧
          ∃ A : ℝ → Fin 2 → ℝ, Measurable A ∧ (∀ p ∈ E₁, ‖A p.2‖ ≤ N ^ ε) ∧
            (∀ i (j : ℤ), ∀ p ∈ E₁, ∀ p' ∈ E₁, p.2 ∈ dI (Tl i) j → p'.2 ∈ dI (Tl i) j →
              ‖F p'.2 - F p.2 - (p'.2 - p.2) • A p.2‖ ≤
                N ^ ε * (((2 : ℝ) ^ Tl i)⁻¹) ^ ((11 : ℝ) / 10)) ∧
            ∀ t : ℝ, Determined E₁ (fun l => zS F (c l) t) univ t ((2 : ℝ) ^ T₀)⁻¹
              (fun l => jet (leafRows F A t) (c l) t 1)
              (N ^ ε * (((2 : ℝ) ^ T₀)⁻¹) ^ ((1 - d) / 32)) ⌊N ^ ε⌋₊

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
