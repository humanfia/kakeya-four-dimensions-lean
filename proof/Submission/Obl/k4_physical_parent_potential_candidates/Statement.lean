-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1032,
-- commit 8e6fd5e0, file PhysicalPotentialStatements.lean (its completion half);
-- namespace renamed to this obligation.
import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket
import Submission.Obl.k4_physical_parent_potential_candidates.StagedInterface

set_option autoImplicit false

namespace Submission.Obl.k4_physical_parent_potential_candidates

noncomputable section

/-- The readable form of the frozen statement of o288: original MK3 heavy groups and
independent-test candidate restoration. The format precedes the output tolerance; every
source and chart remains original. -/
def CompletionAssertion : Prop :=
  mk → ∀ q : ℕ, 2 ≤ q → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < ρ → d₁ + ρ < 1 →
    ∃ precision : ℝ, 1 ≤ precision ∧
      ∀ D : ℕ, max 5186 (864 * (2 * (q + 2)) + 2) ≤ D →
      ∀ J : ℕ, 1 ≤ J → JointJetBound D J →
      ∃ loss : ℝ, 0 < loss ∧ loss ≤ 1 ∧
        ∀ L gain : ℝ, 0 < L → 0 < gain → gain ≤ 1 / 8 →
        ∀ Mp Dp Mr : ℕ, ∃ Mc : ℕ, ∀ Mi : ℕ, Mc ≤ Mi →
        ∀ τ : ℝ, 0 < τ → ∃ Nk₀ : ℝ, 2 ≤ Nk₀ ∧
        ∀ Nk : ℝ, Nk₀ ≤ Nk → ∀ W : ℕ,
        ∀ (ν : Fin W → MeasureTheory.Measure Ln) (B : Fin W → ℝ) (κ : ℝ)
          (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
          (j : Fin C → ℕ) (c u : Fin C → P2) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
          (R : Fin C → Po) (A : Fin C → Set Ln) (F : Fin C → Set Ev)
          (H : Fin W → Set Ev) (ex : Prop) (b : Fin C) (P0 : Po),
          1 ≤ κ →
          (2 : ℝ) ^ T (lev b) ≤ Nk ^ Mr →
          MeasureTheory.IsProbabilityMeasure (ν (γ b)) →
          0 < B (γ b) → B (γ b) ≤ Nk ^ Mr → (B (γ b))⁻¹ ≤ Nk ^ Mr →
          P0.totalDegree ≤ 2 → (∀ e, |P0.coeff e| ≤ Nk ^ Mr) →
          ch Nk Mp Dp κ (T (lev b)) (j b : ℝ) (r (lev b)) (B (γ b)) Set.univ
            (c b) (u b) (Q b) (R b) (A b) (F b) ex →
          j b < 2 ^ T (lev b) → 0 ≤ r (lev b) → r (lev b) + 2 * gain * L ≤ L →
          PhysicalPotentialPacket q precision loss Nk L d₁ gain κ (ν (γ b)) (B (γ b))
            (r (lev b)) (T (lev b)) (j b) (c b) (u b) P0 (A b) (F b) (H (γ b)) →
          cd cc J D Nk L W ν B Mi d₁ ρ gain τ r T C lev γ j A H

end
end Submission.Obl.k4_physical_parent_potential_candidates
