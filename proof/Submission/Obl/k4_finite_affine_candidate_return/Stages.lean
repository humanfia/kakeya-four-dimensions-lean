-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/Stages.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
-- Adapted from this LOT tree, o199, session x0700, commit 711b90f1.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/PrepDiagonal.lean.
import Submission.Obl.k4_finite_affine_candidate_return.Original
import Submission.Obl.k4_finite_affine_candidate_return.EStages

namespace Submission.Obl.k4_finite_affine_candidate_return

open MeasureTheory

noncomputable section

/-- A model index prepared for stage `n` (`N` large, `K` subpower at rate `1/(n+1)`, the
pointwise hypotheses, and the range hypotheses up to `R = n`). -/
def StageGood (d₁ κ₁ ℓ S : ℝ) (n : ℕ) (st : EStage (ℕ × (Fin 6 → ℝ))) : Prop :=
  ((n : ℝ) + 2 ≤ st.N) ∧ (1 ≤ st.K ∧ st.K ≤ st.N ^ (1 / ((n : ℝ) + 1))) ∧ EH1 st ∧
    (∀ R : ℝ, 1 < R → R ≤ n → EH2 d₁ S st R ∧ EH3 d₁ κ₁ ℓ 1 1 st R ∧ EH4 1 st R)

/-- The preparation of one stage `n` on the grid `m, s` with gains `gain, δ₀`. -/
def StageModel (d₁ κ₁ ℓ S η ρ : ℝ) (n : ℕ) (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ) : Prop :=
  ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp : ℕ, ∃ Mc : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
    ∀ r T nw κ C lev par γ j c u Q R A F lst,
      PositivePath ℓ (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀
        Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
      ∀ H : Fin (W k) → Set Incidence,
        (∀ w, MeasurableSet (H w) ∧
          H w ⊆ TerminalInc (W k) C m lev γ F w) →
        (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
          ((ν k w).prod MeasureTheory.volume) (TerminalInc (W k) C m lev γ F w)) ≤
        ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod MeasureTheory.volume) (H w) →
        ∃ st : EStage (ℕ × (Fin 6 → ℝ)), StageGood d₁ κ₁ ℓ S n st ∧
          ∀ R : ℝ, 1 < R → R ≤ n → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ρ / (4 * R) →
            ECand d₁ ℓ 1 st R ε' →
            MixedCandidate (N k) L (W k) (ν k) (B k) Mc d₁ ρ gain ε
              r T C lev γ j u Q A H

/-- A fine stage grid together with its prepared model. -/
def StageReady (d₁ κ₁ ℓ S η ρ : ℝ) (n : ℕ) : Prop :=
  ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ),
    FineGrid m s gain ρ ∧ 0 < gain ∧ gain ≤ 1 / 8 ∧ 0 < δ₀ ∧ δ₀ ≤ ρ * gain ∧
      StageModel d₁ κ₁ ℓ S η ρ n m s gain δ₀

/-- The per-stage models for all parameters (no principle involved). -/
def StageModels : Prop :=
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∀ n : ℕ, StageReady d₁ κ₁ ℓ S η ρ n

end

end Submission.Obl.k4_finite_affine_candidate_return
