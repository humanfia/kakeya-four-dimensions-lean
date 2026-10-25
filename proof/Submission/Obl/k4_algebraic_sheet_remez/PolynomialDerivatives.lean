import Mathlib

namespace Submission.Obl.k4_algebraic_sheet_remez

open Polynomial

/-- Iterated real derivatives of a polynomial are evaluations of its formal
iterated derivatives. -/
theorem iteratedDeriv_polynomial_eval (p : Polynomial ℝ) (q : ℕ) :
    iteratedDeriv q (fun x : ℝ => p.eval x) =
      fun x => ((Polynomial.derivative^[q]) p).eval x := by
  induction q generalizing p with
  | zero => rfl
  | succ q ih =>
    rw [iteratedDeriv_succ']
    have he : deriv (fun x : ℝ => p.eval x) = fun x => p.derivative.eval x :=
      funext (fun _ => p.deriv)
    rw [he, ih]
    rfl

/-- The derivative at the top permitted degree is constant. -/
theorem iteratedDeriv_polynomial_top (p : Polynomial ℝ) (q : ℕ)
    (hp : p.natDegree ≤ q) (x : ℝ) :
    iteratedDeriv q (fun t : ℝ => p.eval t) x = (q.factorial : ℝ) * p.coeff q := by
  rw [iteratedDeriv_polynomial_eval]
  change ((Polynomial.derivative^[q]) p).eval x = _
  have hdeg : (Polynomial.derivative^[q] p).natDegree ≤ 0 :=
    (Polynomial.natDegree_iterate_derivative p q).trans (by omega)
  rw [Polynomial.eq_C_of_natDegree_le_zero hdeg, Polynomial.eval_C,
    Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

end Submission.Obl.k4_algebraic_sheet_remez
