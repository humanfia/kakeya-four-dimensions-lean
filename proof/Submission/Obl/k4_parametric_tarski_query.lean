import Submission.Obl.k4_parametric_tarski_query.ParametricQuery
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.k4_parametric_tarski_query`

Finite polynomial sign partitions control rational coefficient functions and
their degrees. Monic normalization gives symbolic remainders with a uniform
degree bound, so induction determines the Cauchy index on a finite sign
partition. The logarithmic derivative identity identifies this index with
twice the signed count over distinct real roots.

The helper development is adapted from session x0159's work on o050 in this
same LOT tree; each helper file records its source commit and path.
-/

theorem Submission.k4_parametric_tarski_query : ∀ (ι : Type) [Fintype ι] (f g : Polynomial (MvPolynomial ι ℝ)), ∃ (n : ℕ) (q : Fin n → MvPolynomial ι ℝ), ∀ x y : ι → ℝ, (∀ j, SignType.sign (MvPolynomial.eval x (q j)) = SignType.sign (MvPolynomial.eval y (q j))) → (∑ r ∈ (f.map (MvPolynomial.eval x)).roots.toFinset, (SignType.sign ((g.map (MvPolynomial.eval x)).eval r) : ℚ)) = ∑ r ∈ (f.map (MvPolynomial.eval y)).roots.toFinset, (SignType.sign ((g.map (MvPolynomial.eval y)).eval r) : ℚ) := by
  intro ι _ f g
  obtain ⟨n, q, hq⟩ := Submission.Obl.k4_parametric_tarski_query.parametric_tarski_query f g
  exact ⟨n, q, fun x y hxy => hq x y (funext hxy)⟩
