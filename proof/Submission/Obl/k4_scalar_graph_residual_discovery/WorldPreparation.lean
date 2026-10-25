/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldPreparation.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalJetWorld

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

namespace ScalarData

/-- The output needed from the global geometric preparation. The graph
surplus is chosen after the floor exponent, BEFORE the requested accuracy.
The constructed world retains an original failed incidence and its original
full coefficient-bin prior. Worlds need only exist arbitrarily late along
the same dense-failure subsequence, with no rate against a subpower loss. -/
def OriginalWorldPreparation (D : ScalarData) (H : ℕ → ℝ)
    (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence) : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ cζ : ℝ, 0 < cζ → ∀ L : ℝ, 0 < L →
    ∃ L' : ℝ, L ≤ L' ∧ 0 < L' ∧
      ∀ (Hg : ℕ → ℝ) (B : ℝ)
        (G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
        (E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence),
        D.graphData E₀ L' Hg B G E →
        ∀ ε : ℝ, 0 < ε → ∀ α : ℝ, 0 < α → ∀ δ : ℝ, 0 < δ →
        ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
        (∀ j, δ ≤ (D.toQualificationTable B G E).rationalFailureRatio M ε (φ j)) →
        ∃ᶠ j in atTop, ∃ w : OriginalJetWorld D H B G E M ε (φ j),
          w.K ≤ D.N (φ j) ^ α ∧
          D.N (φ j) ^ (-D.κ) / w.K ≤ ((2 : ℝ) ^ D.T (φ j) 1)⁻¹ ∧
          ((2 : ℝ) ^ D.T (φ j) 1)⁻¹ ≤ w.K * D.N (φ j) ^ (-D.κ) ∧
          w.ζ ≤ (((2 : ℝ) ^ D.T (φ j) 1)⁻¹) ^ cζ

/-- Once original worlds have been constructed, higher jets and the
checked original-row transfer give the EXACT discovery interface consumed
by the existing qualification assembly. The graph is fixed throughout all
accuracies and all subsequent dense-failure subsequences. -/
theorem polynomialDiscovery_of_original_world_preparation
    (hjets : Jets.HigherJetsStatement) (D : ScalarData) (H : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ D.N k) (hNt : Tendsto D.N atTop atTop)
    (hH : Subpower D.N H) (hK : Subpower D.N D.K)
    (hd : 0 ≤ D.d) (hd₁ : D.d < 1) (hκ : 0 < D.κ)
    (hscale : ∀ᶠ k in atTop, ((2 : ℝ) ^ D.T k 1)⁻¹ ≤ D.K k * D.N k ^ (-D.κ))
    (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence)
    (hworld : D.OriginalWorldPreparation H E₀) : D.polynomialDiscovery E₀ := by
  intro M hM L hL
  obtain ⟨cζ, hcζ, hconsumer⟩ := original_jet_world_slack_parameters
    hjets D H hN hNt hH hK hd hd₁ hκ hscale M hM
  obtain ⟨L', hLL', hL', hprepare⟩ := hworld M hM cζ hcζ L hL
  refine ⟨L', hLL', hL', ?_⟩
  intro Hg B G E hdata ε hε δ hδ φ hφ hdense
  obtain ⟨α, hα, hgood⟩ := hconsumer ε hε
  have hfrequent := hprepare Hg B G E hdata ε hε α hα δ hδ φ hφ hdense
  obtain ⟨j, hjworld, hjconsumer⟩ := (hfrequent.and_eventually (hφ.eventually hgood)).exists
  obtain ⟨w, hsmall, hlow, hhigh, hfloor⟩ := hjworld
  obtain ⟨i, p, P, hincidence, hbad, hfit⟩ :=
    hjconsumer B G E w hsmall hlow hhigh hfloor
  exact ⟨j, i, p, P, hincidence, hbad, hfit⟩

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
