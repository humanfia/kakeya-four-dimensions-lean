-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod.Statements.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Statements of the polynomial-method foundations

Prop-valued statements used to decouple the files of `PolyMethod`:

* `TuckerStatement`: the grid (cubical) form of Tucker's combinatorial lemma.
* `BorsukUlamStatement`: every continuous odd map `ℝ^(n+1) → ℝ^n` vanishes somewhere on the
  unit sphere of the sup norm.

These are the topological inputs of the Stone–Tukey polynomial ham sandwich theorem and of the
Guth–Katz polynomial partitioning theorem used in Wang–Zahl, Appendix A (Proposition A.4).
-/

namespace WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod

/-- Tucker's lemma on the grid `{-m, …, m}^n`: a labelling by signed indices that is antipodal
on the boundary has two points at sup-distance at most `1` with opposite labels. A label is a
pair `(i, b)`; the opposite label is `(i, !b)`. -/
def TuckerStatement : Prop :=
  ∀ (n m : ℕ), 1 ≤ m → ∀ lab : (Fin n → ℤ) → Fin n × Bool,
    (∀ x : Fin n → ℤ, (∀ i, |x i| ≤ (m : ℤ)) → (∃ i, |x i| = (m : ℤ)) →
      lab (-x) = ((lab x).1, !(lab x).2)) →
    ∃ x y : Fin n → ℤ, (∀ i, |x i| ≤ (m : ℤ)) ∧ (∀ i, |y i| ≤ (m : ℤ)) ∧
      (∀ i, |x i - y i| ≤ 1) ∧ lab y = ((lab x).1, !(lab x).2)

/-- The Borsuk–Ulam theorem: a continuous odd map `ℝ^(n+1) → ℝ^n` has a zero of sup norm `1`. -/
def BorsukUlamStatement : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)), Continuous F → (∀ x, F (-x) = -F x) →
    ∃ x, ‖x‖ = 1 ∧ F x = 0

end WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
