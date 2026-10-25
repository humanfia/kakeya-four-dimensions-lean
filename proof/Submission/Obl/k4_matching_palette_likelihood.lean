import Submission.Obl.k4_matching_palette_likelihood.Assembly
import Submission.Obl.k4_matching_palette_likelihood.Entropy
import ChallengeDeps

set_option linter.unusedVariables false

/-!
# Finite conditional palette likelihood gains

A window's expected positive log gain is at most its conditional entropy drop plus one.
Each conditional entropy lies between zero and `log M`. Summing the entropy drops over all
windows leaves at most `C` boundary terms, giving the required bound.
-/

open Submission.Obl.k4_matching_palette_likelihood

theorem Submission.k4_matching_palette_likelihood : ∀ (n L C M : ℕ) (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ), 1 ≤ C → 1 ≤ M → (∀ x : Fin n, 0 ≤ p x) → (∑ x : Fin n, p x) = 1 → (∀ (k : ℕ) (x y : Fin n), F (k + 1) x = F (k + 1) y → F k x = F k y) → (∀ x : Fin n, ((Finset.univ.filter (fun y : Fin n => 0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M) → (fun q : ℕ → Fin n → ℝ => (∑ a ∈ Finset.range L, ∑ x : Fin n, p x * max 0 (Real.log (q (a + C) x / q a x))) ≤ (C : ℝ) * Real.log (M : ℝ) + (L : ℝ)) (fun k x => (∑ y ∈ Finset.univ.filter (fun y : Fin n => F k y = F k x ∧ Z y = Z x), p y) / (∑ y ∈ Finset.univ.filter (fun y : Fin n => F k y = F k x), p y)) := by
  intro n L C M p F Z hC hM hp hp1 hF hcard
  have hB (k : ℕ) : entropy p (F k) Z ≤ Real.log M := by
    have h := neg_log_card_le_log_likelihood p (F k) Z hM hp hp1
      (refined_palette_card p F Z hF M hcard k)
    simpa only [entropy, posterior, colorMass, fiberMass, neg_neg] using neg_le_neg h
  simpa only [posterior, colorMass, fiberMass] using
    likelihood_of_entropy_bound p F Z hp hp1 hF (Real.log M) hB L C
