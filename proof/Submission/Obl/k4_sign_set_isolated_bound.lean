import Mathlib
import ChallengeDeps
import Submission.Obl.k4_sign_set_isolated_bound.Perturbation
import Submission.Obl.k4_sign_set_isolated_bound.Reduction
set_option linter.unusedVariables false

/-!
# `Submission.k4_sign_set_isolated_bound`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_sign_set_isolated_bound`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_sign_set_isolated_bound/`
belong to this obligation.
-/

namespace Submission.Obl.k4_sign_set_isolated_bound

/-- Nonnegative polynomials of bounded degree have a uniform bound on isolated zeros. -/
theorem isoZeroBound : IsoZeroBound := by
  intro D
  refine ⟨Module.finrank ℝ (MvPolynomial.restrictDegree (Fin 3) ℝ (2 * D + 1)), ?_⟩
  intro f hf hf0 S hS
  have hcard := card_isolatedZeros D f (hf.trans (by omega)) hf0
    (fun x : S => (x : EuclideanSpace ℝ (Fin 3))) Subtype.val_injective
    (fun x => ?_)
  · simpa using hcard
  · obtain ⟨hz, r, hr, hiso⟩ := hS x x.property
    exact ⟨hz, r, hr, fun z hz hd => hiso z hd hz⟩

end Submission.Obl.k4_sign_set_isolated_bound

theorem Submission.k4_sign_set_isolated_bound : ∀ m d : ℕ, ∃ N : ℕ, 0 < N ∧ ∀ (p : Fin m → MvPolynomial (Fin 3) ℝ) (B : Set (Fin m → SignType)) (T : Set (EuclideanSpace ℝ (Fin 3))), (∀ i, (p i).totalDegree ≤ d) → T = {s : EuclideanSpace ℝ (Fin 3) | (fun i => SignType.sign (MvPolynomial.eval (fun k : Fin 3 => s k) (p i))) ∈ B} → {s : EuclideanSpace ℝ (Fin 3) | s ∈ T ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ T, dist z s < ε → z = s}.Finite ∧ {s : EuclideanSpace ℝ (Fin 3) | s ∈ T ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ T, dist z s < ε → z = s}.ncard ≤ N :=
  Submission.Obl.k4_sign_set_isolated_bound.main_of_isoZeroBound
    Submission.Obl.k4_sign_set_isolated_bound.isoZeroBound
