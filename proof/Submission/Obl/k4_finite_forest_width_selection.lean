import Submission.Obl.k4_finite_forest_width_selection.ForestWidthSelection
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.k4_finite_forest_width_selection`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_finite_forest_width_selection`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_finite_forest_width_selection/`
belong to this obligation.
-/

theorem Submission.k4_finite_forest_width_selection : ∀ (m M : ℕ) (ε : ℝ), 0 < m → 0 < ε → ∃ B : ℕ, 0 < B ∧ ∀ (C : ℕ) (lev : Fin C → ℕ) (par : Fin C → Fin C) (vwidth : Fin C → ℝ) (mass : Fin C → ENNReal) (r : ℕ → ℝ) (w q : ℝ), 0 ≤ q → (∀ b, lev b < m ∧ |vwidth b| ≤ (M : ℝ)) → (∀ b, 0 < lev b → lev (par b) + 1 = lev b) → (∀ b, mass b ≠ ⊤) → (∀ a, (∑ b, if 0 < lev b ∧ par b = a then mass b else 0) ≤ mass a) → 0 < (∑ b, if lev b = m - 1 then mass b else 0) → (∀ b, (lev b = 0 → w * r 0 - q ≤ vwidth b) ∧ (0 < lev b → vwidth (par b) + w * (r (lev b) - r (lev (par b))) - q ≤ vwidth b)) → ∃ (C' : ℕ) (emb : Fin C' ↪ Fin C) (par' : Fin C' → Fin C') (nw : ℕ → ℝ), C' ≤ C ∧ (∀ b, 0 < lev (emb b) → emb (par' b) = par (emb b)) ∧ (∀ b, |vwidth (emb b) - nw (lev (emb b))| ≤ ε) ∧ (∀ i, i < m → (∑ b, if lev b = m - 1 then mass b else 0) / (B : ENNReal) ≤ ∑ b, if lev (emb b) = i then mass (emb b) else 0) ∧ (∀ i, i < m → w * r i - (m : ℝ) * (q + 2 * ε) ≤ nw i ∧ nw i + w * (r (m - 1) - r i) - (m : ℝ) * (q + 2 * ε) ≤ nw (m - 1)) := by
  exact Submission.Obl.k4_finite_forest_width_selection.forest_width_selection
