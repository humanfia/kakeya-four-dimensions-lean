import Mathlib
import ChallengeDeps
import Submission.Obl.k4_matching_trimmed_grid.Construction
set_option linter.unusedVariables false

/-!
# `Submission.k4_matching_trimmed_grid`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_matching_trimmed_grid`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_matching_trimmed_grid/`
belong to this obligation.
-/

theorem Submission.k4_matching_trimmed_grid : ∀ (D J : ℕ), 1 ≤ D → D < J → ∀ β : ℕ → ℝ, ((∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j ∧ β j ≤ 2) ∧ (∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ β j = 0)) → (fun r : ℝ → ℝ => (fun l : ℕ → ℝ → ℝ => (fun Admissible : ℕ → Finset ℕ → (ℕ → ℕ) → (ℕ → ℕ) → ℝ → Prop => ∀ δ : ℝ, 0 < δ → ∃ γ : ℝ, 0 < γ ∧ ∀ Q : ℕ, ∃ q : ℕ, Q ≤ q ∧ 1 ≤ q ∧ ∃ (A : Finset ℕ) (m z : ℕ → ℕ), Admissible q A m z γ ∧ 1 + r 1 - δ ≤ ∑ k ∈ A, (1 + 1 / (m k : ℝ)) / (q : ℝ)) (fun (q : ℕ) (A : Finset ℕ) (m z : ℕ → ℕ) (γ : ℝ) => A ⊆ Finset.range q ∧ ∀ k ∈ A, k + 6 * (J + 1) ≤ q ∧ 1 ≤ m k ∧ m k ≤ J ∧ β (m k) < 2 ∧ z (m k) ≤ k ∧ γ ≤ (z (m k) : ℝ) / (q : ℝ) ∧ ∀ x ∈ Set.Icc ((z (m k) : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)), r x = (x - β (m k)) / (m k : ℝ) ∧ (∀ j : ℕ, 1 ≤ j → j ≤ J → j ≠ m k → (x - β j) / (j : ℝ) < r x) ∧ (∀ j : ℕ, j ≤ J → γ ≤ ((J : ℝ) + 1 - (j : ℝ)) * r x - l j x) ∧ (∀ i : ℕ, 1 ≤ i → m k + i ≤ J → γ ≤ l (m k + i) x + (i : ℝ) * r x - β (m k)))) ((fun (j : ℕ) (a : ℝ) => sSup (Set.image (fun x : ℝ => x - (j : ℝ) * r x) (Set.Icc 0 a))))) ((fun a : ℝ => sSup (Set.image (fun j : ℕ => (a - β j) / (j : ℝ)) (Set.Icc 1 J)))) := by
  intro D J hD hDJ β hβ
  have hJ : 1 ≤ J := by omega
  have hz : ∃ d, 1 ≤ d ∧ d ≤ J ∧ β d = 0 := by
    obtain ⟨d, hd, hdD, hdz⟩ := hβ.2
    exact ⟨d, hd, hdD.trans hDJ.le, hdz⟩
  exact Submission.Obl.k4_matching_trimmed_grid.exists_trimmed_grid hJ
    (fun j hj hjJ => (hβ.1 j hj hjJ).1) hz
