-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/StagedInterface.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Interface

namespace Submission.Obl.k4_physical_parent_potential_candidates

/-- The joint dense-set and affine-relative bounds required by the frozen type. -/
def JointJetBound (D J : ℕ) : Prop :=
  ∀ (A : ℝ), 2 ≤ A → ∀ f : P3 → ℝ, exf D f →
    (∀ (E : Set P3) (v : ℝ), MeasurableSet E →
      E ⊆ Metric.closedBall 0 1 → ENNReal.ofReal A⁻¹ ≤ MeasureTheory.volume E →
      0 ≤ v → (∀ x ∈ E, |f x| ≤ v) → ∀ j : ℕ, j ≤ 6 →
      ∀ x ∈ Metric.closedBall 0 2, ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * v) ∧
    (∀ (c : ℝ) (L : P3 →L[ℝ] ℝ) (ε : ℝ), 0 < ε →
      (∀ x ∈ Metric.closedBall 0 1, |f x - c - L x| ≤ ε) →
      ∀ j : ℕ, 2 ≤ j → j ≤ 6 →
      ∀ x ∈ Metric.closedBall 0 2, ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * ε)

/-- The relation degree is fixed before the jet exponent and gain bound. -/
def StagedAt (cc : ℕ) (d₁ κ₁ S η ρ : ℝ) : Prop :=
  ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧
    ∀ J : ℕ, 1 ≤ J → JointJetBound D J →
      ∀ e0 : ℝ, 0 < e0 →
        ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ),
          grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧
            weakds cc J D d₁ κ₁ S η ρ m s gain δ₀ u0

/-- A readable form of the exact frozen obligation. -/
def StagedAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
      0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 → StagedAt cc d₁ κ₁ S η ρ

/-- The geometric input after the elementary parameter ranges have been removed. -/
def HardStagedAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
      0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
        ρ < 1 / 2 → ρ / 16 < κ₁ → StagedAt cc d₁ κ₁ S η ρ

end Submission.Obl.k4_physical_parent_potential_candidates
