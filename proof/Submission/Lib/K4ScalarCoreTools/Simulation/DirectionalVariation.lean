/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/DirectionalVariation.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ffac21c,
Submission/Obl/k4_scalar_mesh_projection/DirectionalVariation.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.FourDirections
import Submission.Lib.K4ScalarCoreTools.Simulation.SymmetricDerivatives
import Submission.Lib.K4ScalarCoreTools.Simulation.PolynomialVariation

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Submission.Lib.K4ScalarSwitching.Switching
open Set MvPolynomial
open Submission.Lib.K4PolynomialPotential

/-- A fixed-degree Markov bound for every coordinate partial on the
normalized box, with constant independent of the number of variables. -/
theorem exists_symmetric_partial_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ z ∈ Icc (-1 : Fin n → ℝ) 1, |eval z P| ≤ E) →
      ∀ z ∈ Icc (-1 : Fin n → ℝ) 1, ∀ i : Fin n, |eval z (pderiv i P)| ≤ C * E := by
  obtain ⟨C, hC, hderiv⟩ := exists_symmetric_polynomial_derivative_constant D
  refine ⟨C, hC, ?_⟩
  intro n P hP E hE hb z hz i
  let q := coordinatePolynomialHom z i P
  have hq : q.natDegree ≤ D := by
    change (MvPolynomial.aeval
      (fun k => if k = i then Polynomial.X else Polynomial.C (z k)) P).natDegree ≤ D
    simpa only [Nat.mul_one] using MvPolynomial.aeval_natDegree_le (n := 1) P hP
      (fun k => if k = i then Polynomial.X else Polynomial.C (z k))
      (fun k => by split_ifs <;> simp)
  have hqb : ∀ s ∈ Icc (-1 : ℝ) 1, |q.eval s| ≤ E := by
    intro s hs
    rw [eval_coordinatePolynomialHom]
    apply hb
    constructor <;> intro k <;> by_cases hk : k = i
    · subst k; simpa using hs.1
    · simpa [Function.update, hk] using hz.1 k
    · subst k; simpa using hs.2
    · simpa [Function.update, hk] using hz.2 k
  have h := hderiv q hq E hE hqb (z i) ⟨hz.1 i, hz.2 i⟩
  simpa only [q, derivative_coordinatePolynomialHom, eval_coordinatePolynomialHom,
    Function.update_eq_self] using h

theorem directionalPartial_totalDegree (P : MvPolynomial (Fin 2) ℝ) (v : ℝ) :
    (directionalPartial v P).totalDegree ≤ P.totalDegree := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_pderiv_le P 0).trans (Nat.sub_le _ _)
  · have h : (C v * pderiv 1 P).totalDegree ≤ (pderiv 1 P).totalDegree := by
      simpa only [C_mul'] using MvPolynomial.totalDegree_smul_le v (pderiv 1 P)
    exact h.trans ((totalDegree_pderiv_le P 1).trans (Nat.sub_le _ _))

/-- A scalar line derivative pays one factor for its velocity and a
fixed-degree factor for the polynomial derivative. -/
theorem exists_directional_partial_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ K E : ℝ, 1 ≤ K → 0 ≤ E →
      (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P| ≤ E) →
      ∀ v : ℝ, |v| ≤ K → ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1,
        |eval z (directionalPartial v P)| ≤ C * K * E := by
  obtain ⟨C, hC, hpartial⟩ := exists_symmetric_partial_constant D
  refine ⟨2 * C, by positivity, ?_⟩
  intro P hP K E hK hE hb v hv z hz
  have h0 := hpartial 2 P hP E hE hb z hz 0
  have h1 := hpartial 2 P hP E hE hb z hz 1
  have hmul := mul_le_mul hv h1 (abs_nonneg _) (by linarith : 0 ≤ K)
  have h := abs_add_le (eval z (pderiv 0 P)) (v * eval z (pderiv 1 P))
  rw [abs_mul] at h
  simp only [directionalPartial, map_add, map_mul, eval_C]
  have hCE : 0 ≤ C * E := mul_nonneg hC.le hE
  nlinarith

/-- A uniform norm and a fixed degree control third directional variation
at nearby physical base points. -/
theorem exists_directional_third_variation_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ K E : ℝ, 1 ≤ K → 0 ≤ E →
      (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P| ≤ E) →
      ∀ v : ℝ, |v| ≤ K → ∀ x ∈ Icc (-1 : Fin 2 → ℝ) 1,
        ∀ y ∈ Icc (-1 : Fin 2 → ℝ) 1,
          |eval y (directionalPartial v (directionalPartial v (directionalPartial v P))) -
            eval x (directionalPartial v (directionalPartial v (directionalPartial v P)))| ≤
              C * K ^ 3 * E * (|y 0 - x 0| + |y 1 - x 1|) := by
  obtain ⟨C, hC, hdir⟩ := exists_directional_partial_constant D
  obtain ⟨V, hV, hvar⟩ := exists_symmetric_square_variation_constant D
  refine ⟨V * C ^ 3, by positivity, ?_⟩
  intro P hP K E hK hE hb v hv
  have hdeg1 := (directionalPartial_totalDegree P v).trans hP
  have hdeg2 := (directionalPartial_totalDegree (directionalPartial v P) v).trans hdeg1
  have hdeg3 := (directionalPartial_totalDegree
    (directionalPartial v (directionalPartial v P)) v).trans hdeg2
  have h1 := hdir P hP K E hK hE hb v hv
  have h2 := hdir (directionalPartial v P) hdeg1 K (C * K * E) hK (by positivity) h1 v hv
  have h3 := hdir (directionalPartial v (directionalPartial v P)) hdeg2 K
    (C * K * (C * K * E)) hK (by positivity) h2 v hv
  intro x hx y hy
  have h := hvar _ hdeg3 (C * K * (C * K * (C * K * E))) (by positivity) h3 x hx y hy
  convert h using 1 <;> ring

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
