/- Adapted from this LOT tree, o040, session x0115, commit 9f7e9a910e7de423611a55b624313eab3641558f,
   Submission/Obl/k4_matching_refinement_exponent/Estimates.lean. -/
import Mathlib

namespace Submission.Obl.k4_matching_cofinal_palette_selection

/-- The frozen finite palette estimate, used as an explicit hypothesis. -/
def PaletteEstimate : Prop :=
  (∀ (n L C M : ℕ) (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ), 1 ≤ C → 1 ≤ M → (∀ x : Fin n, 0 ≤ p x) → (∑ x : Fin n, p x) = 1 → (∀ (k : ℕ) (x y : Fin n), F (k + 1) x = F (k + 1) y → F k x = F k y) → (∀ x : Fin n, ((Finset.univ.filter (fun y : Fin n => 0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M) → (fun q : ℕ → Fin n → ℝ => (∑ a ∈ Finset.range L, ∑ x : Fin n, p x * max 0 (Real.log (q (a + C) x / q a x))) ≤ (C : ℝ) * Real.log (M : ℝ) + (L : ℝ)) (fun k x => (∑ y ∈ Finset.univ.filter (fun y : Fin n => F k y = F k x ∧ Z y = Z x), p y) / (∑ y ∈ Finset.univ.filter (fun y : Fin n => F k y = F k x), p y)))

end Submission.Obl.k4_matching_cofinal_palette_selection
