import Submission.Obl.k4_algebraic_sheet_bound.Coeff

namespace Submission.Obl.k4_algebraic_sheet_bound

open MvPolynomial

/-- Joint continuity of the polynomial family along affine complex lines. -/
theorem continuous_line_eval_polyOf {n D : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    Continuous (fun q : ((Fin (polyDim n D) → ℂ) × EuclideanSpace ℂ (Fin n)) × (ℂ × ℂ) =>
      MvPolynomial.eval
        (Fin.snoc (fun i : Fin n => x i + q.2.1 * (q.1.2 i - x i)) q.2.2)
        (polyOf q.1.1)) := by
  apply continuous_eval_polyOf (by fun_prop)
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    fun_prop
  · simp only [Fin.snoc_castSucc]
    fun_prop

end Submission.Obl.k4_algebraic_sheet_bound
