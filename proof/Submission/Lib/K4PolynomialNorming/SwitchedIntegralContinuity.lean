/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp

open Set MeasureTheory MvPolynomial
open scoped Interval

namespace Submission.Lib.K4PolynomialNorming

/-- The actual sum of signed field integrals depends continuously on the
start, the direction tuple and all endpoint durations. -/
theorem continuous_switched_integral_data {σ κ : Type*}
    [Fintype σ] [Fintype κ] [LinearOrder κ]
    (T : σ → MvPolynomial σ ℝ) :
    Continuous (fun z : ((σ → ℝ) × (κ → σ → ℝ)) × (κ → ℝ) =>
      ∑ k : κ, ∫ s in (0:ℝ)..z.2 k, ∑ a, z.1.2 k a * MvPolynomial.eval
        (fun b => z.1.1 b + ∑ l : κ,
          if l ≤ k then z.1.2 l b * Function.update z.2 k s l else 0) (T a)) := by
  classical
  apply continuous_finsetSum
  intro k _
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ (by fun_prop)
  apply continuous_finsetSum
  intro a _
  apply Continuous.mul (by fun_prop)
  apply (MvPolynomial.continuous_eval (T a)).comp
  apply continuous_pi
  intro b
  apply Continuous.add (by fun_prop)
  apply continuous_finsetSum
  intro l _
  by_cases hl : l ≤ k
  · simp only [ite_eq_left hl]
    apply Continuous.mul (by fun_prop)
    by_cases hlk : l = k
    · subst l
      simp only [Function.update_self]
      fun_prop
    · simp only [Function.update_of_ne hlk]
      fun_prop
  · simp only [ite_eq_right hl]
    exact continuous_const

end Submission.Lib.K4PolynomialNorming
