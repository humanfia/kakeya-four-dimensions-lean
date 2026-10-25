/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/TestConditions.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Raw test predicate from this LOT tree, o156/x0575, SplitStatements.lean,
commit401a7a3; namespace adjusted for o114. -/
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Interface

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SplitStatements

noncomputable def tst : ℝ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → MvPolynomial (Fin 4) ℝ → (ℝ → EuclideanSpace ℝ (Fin 3)) → (ℝ → ℝ) → ℝ → Set ℝ → Prop → Prop :=
  fun Nk a δv P P' zline wline t₀ I cv => (∀ R : MvPolynomial (Fin 4) ℝ, R = P ∨ R = P' → |MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => zline t₀ i) (wline t₀)) R| ≤ δv * Nk ^ a ∧ Nk ^ (-a) ≤ |MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => zline t₀ i) (wline t₀)) (MvPolynomial.pderiv (3 : Fin 4) R)| ∧ |MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => zline t₀ i) (wline t₀)) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ Nk ^ a ∧ (cv → Nk ^ (-a) ≤ MvPolynomial.eval (fun i => zline t₀ i) (disc R))) ∧ ∀ t ∈ I, |MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => zline t i) (wline t)) P| ≤ δv * Nk ^ a ∧ |MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => zline t i) (wline t)) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ Nk ^ a

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SplitStatements
