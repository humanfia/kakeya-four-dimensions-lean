/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/TimePolynomial.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o202, session x0698, commit aacc14fa,
   `Submission/Obl/k4_horizontal_subcritical_rate_candidates/TimePolynomial.lean`. Original imports of accepted libraries are retained. -/
import Submission.Lib.K4PolynomialRemez
import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry

/-! Coefficient control for the quadratic time signal selected in Proposition 9.7. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Polynomial Set MeasureTheory

noncomputable def quadraticTimePolynomial (b : Fin 3 → ℝ) : Polynomial ℝ :=
  C (b 0) + C (b 1) * X ^ 1 + C (b 2) * X ^ 2

lemma quadraticTimePolynomial_degree (b : Fin 3 → ℝ) :
    (quadraticTimePolynomial b).natDegree ≤ 2 := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    exact max_le (by simp) ((natDegree_C_mul_X_pow_le _ 1).trans (by norm_num))
  · exact natDegree_C_mul_X_pow_le _ 2

lemma quadraticTimePolynomial_eval (b : Fin 3 → ℝ) (t : ℝ) :
    (quadraticTimePolynomial b).eval t = b 0 + b 1 * t + b 2 * t ^ 2 := by
  simp [quadraticTimePolynomial]

/-- Recover exactly the three coefficients using the accepted unit-interval interpolation. -/
lemma timePolynomial_recovered_coefficient (b : Fin 3 → ℝ) (i : Fin 3) :
    (Submission.Obl.k4_horizon_chart_assembly.quadraticCoefficients
      (fun t => (quadraticTimePolynomial b).eval t)) i = b i := by
  fin_cases i <;>
    simp [Submission.Obl.k4_horizon_chart_assembly.quadraticCoefficients,
      quadraticTimePolynomial] <;> ring

/-- A quadratic fitting a bounded shared signal on a long time set has bounded coefficients. -/
lemma timePolynomial_coeff_bound {b : Fin 3 → ℝ} {G : ℝ → ℝ} {S : Set ℝ}
    {η K E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (0 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hG : ∀ t ∈ S, |G t| ≤ K)
    (hfit : ∀ t ∈ S, |(quadraticTimePolynomial b).eval t - G t| ≤ E)
    (i : Fin 3) : |b i| ≤ 17 * (24 / η) ^ 2 * (K + E) := by
  have hlocal : ∀ t ∈ S, |(quadraticTimePolynomial b).eval t| ≤ K + E := by
    intro t ht
    have htri := abs_add_le ((quadraticTimePolynomial b).eval t - G t) (G t)
    have heq : (quadraticTimePolynomial b).eval t - G t + G t =
        (quadraticTimePolynomial b).eval t := by ring
    rw [heq] at htri
    linarith [hG t ht, hfit t ht]
  have hfull := Submission.Lib.K4PolynomialRemez.polynomial_remez_unit
    (quadraticTimePolynomial b) 2 (quadraticTimePolynomial_degree b) S hη hη1
    (by positivity) hS hmass hlocal
  have hnorm := Submission.Obl.k4_horizon_chart_assembly.quadraticCoefficients_norm_le hfull
  have hi := (PiLp.norm_apply_le
    (Submission.Obl.k4_horizon_chart_assembly.quadraticCoefficients
      (fun t => (quadraticTimePolynomial b).eval t)) i).trans hnorm
  rw [timePolynomial_recovered_coefficient, Real.norm_eq_abs] at hi
  norm_num at hi
  simpa only [mul_assoc] using hi

end Submission.Obl.k4_subcritical_corrected_scalar_charts
