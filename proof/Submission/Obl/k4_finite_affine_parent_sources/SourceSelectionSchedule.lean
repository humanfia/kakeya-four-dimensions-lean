-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceSchedule

/-!
# The outer schedule of the selection component

`SourceSelectionLateSpec` is `SourceSelectionSpec` with "every late enough sample" replaced by
"every sample with the lateness facts `LateFacts`" for menus, tolerances and constants chosen
after `ε` (and before the sample), and with the slack bounded by an explicit positive function
`σb` of the two tail powers. `sourceSelectionSpec_of_late` chooses the tail powers and the
cutoff (`exists_lateFacts`) and the slack bound `σp := σb cd ca`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Filter

noncomputable section

/-- **The selection component with explicit lateness facts.** -/
def SourceSelectionLateSpec : Prop :=
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∀ n : ℕ, 2 ≤ n →
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
    ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ gain : ℝ, 0 < gain → gain ≤ g₀ →
    ∀ (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ), FineGrid m s gain ρ → 0 < δ₀ → δ₀ ≤ ρ * gain →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
      (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
      ∀ Mp Dp : ℕ, ∃ Mprep : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ (Gd Ga Gc : ℕ) (q : Fin Gd → ℝ) (τd : ℝ) (w : Fin Ga → ℝ) (τa N₀ eK : ℝ)
        (a C : Fin Gc → ℝ) (σb : ℝ → ℝ → ℝ),
        (∀ i, q i ∈ Icc 0 L) ∧ 0 < τd ∧ (∀ j, 0 < w j ∧ w j ≤ η * L) ∧ 0 < τa ∧ 0 < eK ∧
        (∀ l, 0 < a l) ∧ (∀ cd ca : ℝ, 0 < cd → 0 < ca → 0 < σb cd ca) ∧
        ∀ cd ca : ℝ, 0 < cd → 0 < ca → ∀ σ : ℝ, 0 < σ → σ ≤ σb cd ca → ∀ k,
        LateFacts (N k) (K k) L S (W k) (ω k) (ν k) (E k) (B k) f (g k) (G k) q τd cd w τa ca
          N₀ eK a C →
        ∀ p : PathData (W k), p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ →
        ∀ H : Fin (W k) → Set Incidence,
          (∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc (W k) p.C m p.lev p.world p.counted w) →
          (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
            ((ν k w).prod volume) (TerminalInc (W k) p.C m p.lev p.world p.counted w)) ≤
          ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod volume) (H w) →
          MixedCandidate (N k) L (W k) (ν k) (B k) Mprep d₁ ρ gain ε
            p.r p.T p.C p.lev p.world p.bin p.velocity p.frame p.assigned H ∨
          SelectionOutput p n m s d₁ ℓ S ρ u δ₀ ε (N k) L (ν k) (B k) H

/-- **The outer schedule:** the selection component from its lateness form. -/
theorem sourceSelectionSpec_of_late (h : SourceSelectionLateSpec) : SourceSelectionSpec := by
  intro d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  obtain ⟨u₀, hu₀, hU⟩ := h d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  refine ⟨u₀, hu₀, fun u hu hu' => ?_⟩
  obtain ⟨g₀, hg₀, hG⟩ := hU u hu hu'
  refine ⟨g₀, hg₀, fun gain hg hg' m s δ₀ hgrid hδ₀ hδ₀' => ?_⟩
  intro N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨Mprep, hP⟩ := hG gain hg hg' m s δ₀ hgrid hδ₀ hδ₀' N K L d W ω ν E P B f g G
    hprob hprof Mp Dp
  refine ⟨Mprep, fun ε hε => ?_⟩
  obtain ⟨Gd, Ga, Gc, q, τd, w, τa, N₀, eK, a, C, σb, hq, hτd, hw, hτa, heK, ha, hσb, hsample⟩ :=
    hP ε hε
  obtain ⟨cd, ca, hcd, hca, hlate⟩ :=
    exists_lateFacts hprob q hq hτd w hw hτa N₀ heK a C ha
  obtain ⟨kp, hkp⟩ := eventually_atTop.mp hlate
  exact ⟨σb cd ca, hσb cd ca hcd hca, kp, fun σ hσ hσ' k hk p hp H hH hmass =>
    hsample cd ca hcd hca σ hσ hσ' k (hkp k hk) p hp H hH hmass⟩

end

end Submission.Obl.k4_finite_affine_parent_sources
