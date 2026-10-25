-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/Monotonicity.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.Candidates
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory

/-- A smaller path exponent is admissible at every larger exponent. -/
theorem path_slack_mono
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (E : Fin W → Set Incidence) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (κ : ℝ) (C : ℕ)
    (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set Trajectory)
    (F : Fin C → Set Incidence)
    (lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C))
    (σ' : ℝ) (hN : 1 ≤ Nk) (hσ : σ ≤ σ')
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ
      C lev par γ j c u Q R A F lst) :
    path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ' r T nw κ
      C lev par γ j c u Q R A F lst :=
  ⟨hp.1, hp.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN hσ), hp.2.2⟩

/-- Enlarging the common output slack and polynomial complexity preserves the
system and the same original-law observation lists. -/
theorem system_mono
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (M D M' D' : ℕ) (τ τ' r₂ : ℝ) (T₂ : ℕ)
    (extra : Matrix (Fin 2) (Fin 2) ℝ → Prop)
    (hN : 1 ≤ Nk) (hM : M ≤ M') (hD : D ≤ D') (hτ : τ ≤ τ') (hB : ∀ w, 0 ≤ B w)
    (hs : system Nk L W ω ν E B M D τ r₂ T₂ extra) :
    system Nk L W ω ν E B M' D' τ' r₂ T₂ extra := by
  have hNkpos : 0 < Nk := lt_of_lt_of_le zero_lt_one hN
  have hslack : Nk ^ τ ≤ Nk ^ τ' := Real.rpow_le_rpow_of_exponent_le hN hτ
  rcases hs with ⟨C, γ, j, c, u, Q, R, A, F, lst, hC, hd, hl, hc, hm⟩
  refine ⟨C, γ, j, c, u, Q, R, A, F, lst,
    hC.trans (pow_le_pow_right₀ hN hM), hd, (fun w o => (hl w o).trans hslack), ?_, ?_⟩
  · intro b
    exact ⟨Submission.Obl.k4_quadratic_atlas_normalization.chart_mono
      hN hM hD (Real.rpow_pos_of_pos hNkpos _) hslack (hB _) (hc b).1 id, (hc b).2⟩
  · exact (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN
      (neg_le_neg hτ))).trans hm

/-- Monotonicity of the width alternative, retaining its level and determinant gain. -/
theorem width_mono
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (gain : ℝ)
    (M D M' D' : ℕ) (τ τ' : ℝ)
    (hN : 1 ≤ Nk) (hM : M ≤ M') (hD : D ≤ D') (hτ : τ ≤ τ') (hB : ∀ w, 0 ≤ B w)
    (hs : width Nk L W ω ν E B m r T nw gain M D τ) :
    width Nk L W ω ν E B m r T nw gain M' D' τ' := by
  rcases hs with ⟨i, hi, hr, hs⟩
  exact ⟨i, hi, hr, system_mono Nk L W ω ν E B M D M' D' τ τ' (r i) (T i) _
    hN hM hD hτ hB hs⟩

end Submission.Obl.k4_quadratic_finite_greedy_cover
