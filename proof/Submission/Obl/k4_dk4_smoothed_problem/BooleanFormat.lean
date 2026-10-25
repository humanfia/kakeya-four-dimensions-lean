/- Adapted within this LOT tree from o006/x0154 and x0006, Submission/Obl/k4_core/FloorTables.lean:
the format definition and intersection lemma only. -/

import Mathlib

/-!
# Polynomial sign descriptions of finite floor lookup tables

A bounded table of base-cell or hidden-bin labels can be implemented by polynomial
threshold tests. This is the elementary temperedness part of the finite-table
selection in Lemma a01:flattening; no quantified-variable elimination is used.
-/

namespace Submission.Obl.k4_dk4_smoothed_problem

open Set

/-- The Boolean polynomial format used in the frozen tempered-data interface. -/
def HasBoolPolynomialFormat {σ X : Type*} (coord : X → σ → ℝ)
    (S : Set X) (m d : ℕ) : Prop :=
  ∃ p : Fin m → MvPolynomial σ ℝ, (∀ i, (p i).totalDegree ≤ d) ∧
    ∃ b : (Fin m → Bool) → Bool,
      ∀ x, x ∈ S ↔ b (fun i => decide (0 ≤ MvPolynomial.eval (coord x) (p i))) = true

/-- Intersecting two lookup predicates concatenates their polynomial tests. -/
theorem HasBoolPolynomialFormat.inter {σ X : Type*} {coord : X → σ → ℝ}
    {S T : Set X} {m n d e : ℕ}
    (hS : HasBoolPolynomialFormat coord S m d)
    (hT : HasBoolPolynomialFormat coord T n e) :
    HasBoolPolynomialFormat coord (S ∩ T) (m + n) (max d e) := by
  obtain ⟨p, hp, b, hb⟩ := hS
  obtain ⟨q, hq, c, hc⟩ := hT
  refine ⟨Fin.addCases p q, ?_,
    (fun v => b (fun i => v (Fin.castAdd n i)) && c (fun i => v (Fin.natAdd m i))), ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using (hp j).trans (le_max_left d e)
    · simpa only [Fin.addCases_right] using (hq j).trans (le_max_right d e)
  · intro x
    simpa only [Set.mem_inter_iff, Fin.addCases_left, Fin.addCases_right, Bool.and_eq_true]
      using and_congr (hb x) (hc x)

end Submission.Obl.k4_dk4_smoothed_problem
