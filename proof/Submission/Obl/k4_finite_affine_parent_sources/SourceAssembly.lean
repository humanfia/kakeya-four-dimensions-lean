-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceGood

/-!
# `SourcePreparation` from per-sample source facts

`SourceSamples` is `SourcePreparation` with its per-sample conclusion replaced by: an
original mixed candidate, or one `SourceData` whose `SourceData.Facts` hold (with some slack
constants `J, τ`). `sourcePreparation_of_samples` derives the frozen `SourcePreparation`
through `SourceData.Facts.good`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory

noncomputable section

/-- The per-sample form of the source preparation. -/
def SourceSamples : Prop :=
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∀ n : ℕ, 2 ≤ n →
    ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ unit : ℝ),
      FineGrid m s gain ρ ∧ 0 < gain ∧ gain ≤ 1 / 8 ∧ 0 < δ₀ ∧ δ₀ ≤ ρ * gain ∧
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
      (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
      ∀ Mp Dp : ℕ, ∃ M : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∀ p : PathData (W k), p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁
          m s δ₀ Mp Dp σ →
      ∀ H : Fin (W k) → Set Incidence,
        (∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc (W k) p.C m p.lev p.world p.counted w) →
        (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
          ((ν k w).prod volume) (TerminalInc (W k) p.C m p.lev p.world p.counted w)) ≤
        ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod volume) (H w) →
        MixedCandidate (N k) L (W k) (ν k) (B k) M d₁ ρ gain ε
          p.r p.T p.C p.lev p.world p.bin p.velocity p.frame p.assigned H ∨
        ∃ (D : SourceData p) (J τ : ℝ),
          D.Facts n M m d₁ κ₁ ℓ S ρ gain ε unit (N k) L J τ (ν k) (B k) H

/-- **`SourcePreparation` from per-sample source facts.** -/
theorem sourcePreparation_of_samples (h : SourceSamples) : SourcePreparation := by
  intro d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  obtain ⟨m, s, gain, δ₀, unit, hgrid, hg, hg', hδ, hδ', hrest⟩ :=
    h d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  refine ⟨m, s, gain, δ₀, unit, hgrid, hg, hg', hδ, hδ', ?_⟩
  intro N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨M, hM⟩ := hrest N K L d W ω ν E P B f g G hprob hprof Mp Dp
  refine ⟨M, fun ε hε => ?_⟩
  obtain ⟨σ, hσ, k₀, hk⟩ := hM ε hε
  refine ⟨σ, hσ, k₀, fun k hk₀ p hp H hH hmass => ?_⟩
  rcases hk k hk₀ p hp H hH hmass with hcand | ⟨D, J, τ, hf⟩
  · exact Or.inl hcand
  · exact Or.inr ⟨D.stage (N k) L unit (ν k) (B k), SourceData.Facts.good D hp hf⟩

end

end Submission.Obl.k4_finite_affine_parent_sources
