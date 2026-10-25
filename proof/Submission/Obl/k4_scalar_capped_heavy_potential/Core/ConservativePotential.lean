/- Adapted (namespace renamed) from LOT tree oai_074 (this tree), obligation o062,
session x0511, branch x0511, commit f33e26edad,
Submission/Lib/K4ScalarCoreTools/Simulation/ConservativePotential.lean (an unadmitted lib candidate).
Its own credits follow unchanged. -/

/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/ConservativePotential.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ffac21c,
Submission/Obl/k4_scalar_mesh_projection/ConservativePotential.lean.
-/

import Submission.Lib.K4PolynomialPotential
import Submission.Obl.k4_scalar_capped_heavy_potential.Core.CoefficientMass

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching


open Set MvPolynomial
open Submission.Lib.K4PolynomialPotential

/-- On the normalized box, evaluation costs no more than the sum of the
absolute coefficients. The coefficient mass and its degree bound are
imported from the accepted native atlas library. -/
theorem eval_le_coefficientMass_on_unit {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : x ∈ Icc (-1 : Fin n → ℝ) 1) :
    |eval x P| ≤ Submission.Obl.k4_scalar_capped_heavy_potential.Core.CoefficientMass.coefficientMass P := by
  classical
  rw [MvPolynomial.eval_eq']
  calc
    _ ≤ ∑ e ∈ P.support, |P.coeff e * ∏ i : Fin n, x i ^ e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ P.support, |P.coeff e| := Finset.sum_le_sum fun e _ => by
      rw [abs_mul, Finset.abs_prod]
      have hprod : (∏ i : Fin n, |x i ^ e i|) ≤ 1 := by
        apply Finset.prod_le_one₀
        · intro i _
          exact abs_nonneg _
        · intro i _
          rw [abs_pow]
          exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨hx.1 i, hx.2 i⟩)
      exact (mul_le_mul_of_nonneg_left hprod (abs_nonneg _)).trans_eq (mul_one _)

/-- The coefficient curl bound from original switched paths feeds the
accepted bounded polynomial potential without any new analytic premise. -/
theorem bounded_potential_of_curl_coefficients (A B : MvPolynomial (Fin 2) ℝ)
    (D : ℕ) (hA : A.totalDegree ≤ D) (hB : B.totalDegree ≤ D)
    (K E : ℝ) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hrows : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z A| ≤ K ∧ |eval z B| ≤ K)
    (hcoeff : ∀ e : Fin 2 →₀ ℕ, |(pderiv 0 B - pderiv 1 A).coeff e| ≤ E) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P.totalDegree ≤ D + 2 ∧ pderiv 1 P = B ∧
      eval (0 : Fin 2 → ℝ) P = 0 ∧
      ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P| ≤ 2 * K ∧
        |eval z (pderiv 0 P) - eval z A| ≤ ((D + 1) ^ 2 : ℕ) * E := by
  have hdeg : (pderiv 0 B - pderiv 1 A).totalDegree ≤ D := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    exact max_le ((totalDegree_pderiv_le B 0).trans ((Nat.sub_le _ _).trans hB))
      ((totalDegree_pderiv_le A 1).trans ((Nat.sub_le _ _).trans hA))
  have hcurl : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |eval z (pderiv 0 B - pderiv 1 A)| ≤ ((D + 1) ^ 2 : ℕ) * E := by
    intro z hz
    exact (eval_le_coefficientMass_on_unit _ z hz).trans
      (Submission.Obl.k4_scalar_capped_heavy_potential.Core.CoefficientMass.coefficientMass_le_of_coeff_bound
        _ hdeg hE hcoeff)
  exact exists_bounded_polynomial_potential A B hA hB hK (by positivity)
    (fun z hz => (hrows z hz).1) (fun z hz => (hrows z hz).2) hcurl

end Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching
