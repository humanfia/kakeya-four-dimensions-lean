-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/PathFacts.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.PrioritySets

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

/-- The finite terminal union is measurable under the original path laws. -/
theorem terminalUnion_measurable
    (W C m : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set Incidence)
    (hFm : ∀ b, MeasurableSet (F b)) (w : Fin W) :
    MeasurableSet (terminalUnion m lev γ F w) := by
  classical
  have heq : terminalUnion m lev γ F w =
      selectedUnion (Finset.univ.filter (fun b => lev b = m - 1)) γ F w := by
    ext p
    simp only [terminalUnion, selectedUnion, mem_ofPred_eq, mem_iUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  rw [heq]
  exact selectedUnion_measurable _ γ F (fun b _ => hFm b) w

/-- Every terminal incidence remains inside its original world support. -/
theorem terminalUnion_subset
    (W C m : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (F : Fin C → Set Incidence) (E : Fin W → Set Incidence)
    (hF : ∀ b, F b ⊆ E (γ b)) (w : Fin W) :
    terminalUnion m lev γ F w ⊆ E w := by
  rintro p ⟨b, _, hb, hp⟩
  simpa only [hb] using hF b hp

/-- The elementary original-law facts used by the candidate-cover assembly.
No conditional or normalized replacement of a world prior occurs. -/
theorem prob_basic
    (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence)
    (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (hp : prob N K L d S η W ω ν E P B f g G) :
    (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ 0 < L ∧
    (∀ k w, 0 ≤ ω k w) ∧ (∀ k, (∑ w, ω k w) = 1) ∧
    (∀ k w, IsProbabilityMeasure (ν k w)) ∧ (∀ k w, 0 < B k w) ∧
    (∀ k w, E k w ⊆ Set.univ ×ˢ Icc (0 : ℝ) 1) := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd', hS, hη, hrest⟩
  obtain ⟨M, D, hdata⟩ := hrest.1
  refine ⟨hN, hNt, hL, (fun k => (hdata k).2.1),
    (fun k => (hdata k).2.2.1), ?_, ?_, ?_⟩
  · intro k w
    exact ((hdata k).2.2.2.1 w).1
  · intro k w
    exact ((hdata k).2.2.2.1 w).2.1
  · intro k w
    rcases ((hdata k).2.2.2.1 w) with ⟨_, _, _, _, _, _, _, _, hE, _⟩
    exact hE

end Submission.Obl.k4_quadratic_finite_greedy_cover
