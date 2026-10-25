/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/SymmetricDerivatives.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ffac21c,
Submission/Obl/k4_scalar_mesh_projection/SymmetricDerivatives.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.PolynomialVariation

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Submission.Lib.K4ScalarSwitching.Switching
open Set

/-- Uniform polynomial derivative comparison on the symmetric interval. -/
theorem exists_symmetric_polynomial_derivative_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Polynomial ℝ, p.natDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ Icc (-1 : ℝ) 1, |p.eval t| ≤ E) →
      ∀ x ∈ Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ C * E := by
  obtain ⟨C, hC, hderiv⟩ := exists_uniform_polynomial_derivative_constant D
  refine ⟨C, hC, ?_⟩
  intro p hp E hE hb x hx
  let a : Polynomial ℝ := Polynomial.C (-1) + Polynomial.C 2 * Polynomial.X
  let q := p.comp a
  have ha : a.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp))
  have hq : q.natDegree ≤ D :=
    Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul hp ha).trans_eq (Nat.mul_one D))
  have hqb : ∀ t ∈ Icc (0 : ℝ) 1, |q.eval t| ≤ E := by
    intro t ht
    have hpoint : -1 + 2 * t ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    simpa only [q, a, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using hb _ hpoint
  have hu : (x + 1) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have h := hderiv q hq E hE hqb _ hu
  have hd : q.derivative.eval ((x + 1) / 2) = p.derivative.eval x * 2 := by
    simp only [q, a, Polynomial.derivative_comp, Polynomial.derivative_add,
      Polynomial.derivative_C, Polynomial.derivative_mul, Polynomial.derivative_X,
      zero_add, zero_mul, one_mul, mul_one, Polynomial.eval_mul,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    rw [show -1 + 2 * ((x + 1) / 2) = x by ring]
    ring
  rw [hd, abs_mul] at h
  norm_num at h
  linarith [abs_nonneg (p.derivative.eval x)]

/-- Three iterations keep the degree fixed and cost one comparison constant
per derivative. -/
theorem exists_symmetric_polynomial_third_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Polynomial ℝ, p.natDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ Icc (-1 : ℝ) 1, |p.eval t| ≤ E) →
      ∀ x ∈ Icc (-1 : ℝ) 1,
        |p.derivative.derivative.derivative.eval x| ≤ C * E := by
  obtain ⟨C, hC, hderiv⟩ := exists_symmetric_polynomial_derivative_constant D
  refine ⟨C ^ 3, by positivity, ?_⟩
  intro p hp E hE hb
  have hd (q : Polynomial ℝ) : q.derivative.natDegree ≤ q.natDegree :=
    q.natDegree_derivative_le.trans (Nat.sub_le _ _)
  have h1 := hderiv p hp E hE hb
  have h2 := hderiv p.derivative ((hd p).trans hp) (C * E) (by positivity) h1
  have h3 := hderiv p.derivative.derivative
    ((hd p.derivative).trans ((hd p).trans hp)) (C * (C * E)) (by positivity) h2
  intro x hx
  convert h3 x hx using 1 <;> ring

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
