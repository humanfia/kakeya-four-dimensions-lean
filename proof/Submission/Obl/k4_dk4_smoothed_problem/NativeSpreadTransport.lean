import Submission.Obl.k4_dk4_smoothed_problem.NativePrior

open MeasureTheory Set

namespace Submission.Obl.k4_dk4_smoothed_problem.Framework

theorem packLine_baseObservation (p : PairCoefficients) (t : ℝ) :
    baseObservation (packLine p, t) =
      WithLp.toLp 2 ![t, p.1 0 + t * p.2 0, p.1 1 + t * p.2 1] := by
  have hb0 := packLine_coordinate p 0
  have hb1 := packLine_coordinate p 1
  have hs0 := packLine_slope_coordinate p 0
  have hs1 := packLine_slope_coordinate p 1
  ext j
  fin_cases j <;> simp_all [baseObservation, trajectoryPoint]

theorem nativePrior_base_mass_eq {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin 3 → ℝ) (U : Set (EuclideanSpace ℝ (Fin 3))) :
    (nativePrior r b s).prod volume
        {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ baseObservation p ∈ U} =
      (FiniteSmoothing.smoothedPrior r b s).prod volume
        {p | p.2 ∈ Icc (0 : ℝ) 1 ∧
          (WithLp.toLp 2 ![p.2, p.1.1 0 + p.2 * p.1.2 0,
            p.1.1 1 + p.2 * p.1.2 1] : EuclideanSpace ℝ (Fin 3)) ∈ U} := by
  rw [nativePrior_prod_apply hn hr]
  congr 1

end Submission.Obl.k4_dk4_smoothed_problem.Framework
