/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit f3582cb1, file DiscoveryBudgetStatement.lean.
   Helper namespace and imports renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryBudget

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

/-- The numerical existence assertion sufficient for actual original
world preparation. Fixed graph precision precedes all graph arrays and
accuracy budgets; every field of the sample certificate is numerical. -/
def DiscoveryBudgetExistenceStatement : Prop :=
  ∀ (N K H : ℕ → ℝ) (m : ℕ → ℕ) (h : ℕ → ℝ),
    (∀ k, 2 ≤ N k) → Tendsto N atTop atTop → Subpower N K → Subpower N H →
    (∀ k, 1 ≤ m k ∧ N k ^ (1 / (m k : ℝ)) ≤ H k) →
    ∀ d κ S : ℝ, 0 ≤ d → d ≤ 1 → 0 < κ → 0 < S →
    (∀ k, 0 < h k) →
    (∀ᶠ k in atTop, N k ^ (-κ) / K k ≤ h k ∧ h k ≤ K k * N k ^ (-κ)) →
    ∀ M : ℕ, 2 ≤ M → ∀ cζ : ℝ, 0 < cζ → ∀ L : ℝ, 0 < L →
    ∀ Cmk : ℝ, 0 < Cmk →
    ∃ C C₁ : ℕ, 1 ≤ C ∧ 1 ≤ C₁ ∧ ∃ L' : ℝ, L ≤ L' ∧ 0 < L' ∧ (C₁ : ℝ) ≤ L' ∧
      ∀ Hg : ℕ → ℝ, Subpower N Hg → ∀ B : ℝ, L' + 10 ≤ B →
        ∀ α : ℝ, 0 < α → ∀ δ : ℝ, 0 < δ →
        ∃ J₁ J₂ : ℕ, 1 ≤ J₁ ∧ 1 ≤ J₂ ∧ ∃ T : ℝ, 1 < T ∧
          ∀ᶠ k in atTop, Nonempty (DiscoveryBudget (N k) (H k) (Hg k) (K k) d S L' B (h k)
            δ α cζ Cmk T (m k) M C₁ C J₁ J₂)

end Submission.Obl.k4_scalar_graph_residual_discovery
