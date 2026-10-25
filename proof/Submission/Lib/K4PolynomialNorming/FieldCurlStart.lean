/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open Set MeasureTheory MvPolynomial
namespace Submission.Lib.K4PolynomialNorming
def largeFieldCurlStart {X : Type*} (T : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (base : X → Fin 3 → ℝ) (threshold : ℝ) : Set X :=
  {x | ∃ i j : Fin 3, threshold <
    |MvPolynomial.eval (base x) (pderiv j (T i))-MvPolynomial.eval (base x) (pderiv i (T j))|}

theorem largeFieldCurlStart_measurable {X : Type*} [MeasurableSpace X]
    (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (base : X → Fin 3 → ℝ)
    (hbase : Measurable base) (threshold : ℝ) :
    MeasurableSet (largeFieldCurlStart T base threshold) := by
  unfold largeFieldCurlStart
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  exact measurableSet_lt measurable_const (continuous_abs.measurable.comp
    (((MvPolynomial.continuous_eval (pderiv j (T i))).measurable.comp hbase).sub
      ((MvPolynomial.continuous_eval (pderiv i (T j))).measurable.comp hbase)))


end Submission.Lib.K4PolynomialNorming
