-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/PolynomialDirectional.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/PolynomialDirectional.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/PolynomialDirectional.lean
-- Earlier source attributions below are retained.
import Mathlib
import Submission.Lib.K4QuadraticSheets.QuadTest

-- The curve result generalizes the real Fin 3 statement in the accepted
-- o180 file k4_approximate_conic_taylor_decomposition/Forms.lean.

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial

section Algebra

variable {𝕜 : Type*} [CommSemiring 𝕜]

/-- The formal polynomial derivative in a fixed direction. -/
def complexPolynomialDirectional {n : ℕ} (v : Fin n → 𝕜)
    (P : MvPolynomial (Fin n) 𝕜) : MvPolynomial (Fin n) 𝕜 :=
  ∑ i, C (v i) * pderiv i P

lemma complexPolynomialDirectional_C {n : ℕ} (v : Fin n → 𝕜) (c : 𝕜) :
    complexPolynomialDirectional v (C c) = 0 := by
  simp [complexPolynomialDirectional]

lemma complexPolynomialDirectional_add {n : ℕ} (v : Fin n → 𝕜)
    (P Q : MvPolynomial (Fin n) 𝕜) :
    complexPolynomialDirectional v (P + Q) =
      complexPolynomialDirectional v P + complexPolynomialDirectional v Q := by
  simp [complexPolynomialDirectional, map_add, mul_add, Finset.sum_add_distrib]

lemma complexPolynomialDirectional_X {n : ℕ} (v : Fin n → 𝕜) (j : Fin n) :
    complexPolynomialDirectional v (X j) = C (v j) := by
  classical
  simp [complexPolynomialDirectional, pderiv_X, Pi.single_apply]

lemma complexPolynomialDirectional_mul {n : ℕ} (v : Fin n → 𝕜)
    (P Q : MvPolynomial (Fin n) 𝕜) :
    complexPolynomialDirectional v (P * Q) =
      complexPolynomialDirectional v P * Q + P * complexPolynomialDirectional v Q := by
  simp only [complexPolynomialDirectional, Derivation.leibniz, smul_eq_mul]
  calc
    _ = ∑ i, ((C (v i) * pderiv i P) * Q + P * (C (v i) * pderiv i Q)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

/-- The degree control imports the accepted partial-derivative bound. -/
theorem complexPolynomialDirectional_totalDegree {n : ℕ} (v : Fin n → 𝕜)
    (P : MvPolynomial (Fin n) 𝕜) :
    (complexPolynomialDirectional v P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_mul _ _).trans
  have h := Submission.Lib.K4QuadraticSheets.totalDegree_pderiv_le' P i
    (d := P.totalDegree) (Nat.le_succ _)
  simpa only [totalDegree_C, zero_add] using h

end Algebra

section Calculus

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Formal coordinate differentiation computes the actual derivative along
every coordinatewise differentiable curve, in arbitrary dimension and over
any nontrivially normed field. -/
theorem hasDerivAt_eval_complex_curve {n : ℕ} (P : MvPolynomial (Fin n) 𝕜)
    (z : 𝕜 → Fin n → 𝕜) (v : Fin n → 𝕜) (t : 𝕜)
    (hz : ∀ i, HasDerivAt (fun s => z s i) (v i) t) :
    HasDerivAt (fun s => eval (z s) P) (eval (z t) (complexPolynomialDirectional v P)) t := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa only [eval_C, complexPolynomialDirectional_C, map_zero] using hasDerivAt_const t c
  | add p q hp hq =>
    simpa only [complexPolynomialDirectional_add, map_add] using hp.fun_add hq
  | mul_X p i hp =>
    simpa only [complexPolynomialDirectional_mul, complexPolynomialDirectional_X,
      map_add, map_mul, eval_X, eval_C] using hp.fun_mul (hz i)

theorem hasDerivAt_eval_complex_line {n : ℕ} (P : MvPolynomial (Fin n) 𝕜)
    (a v : Fin n → 𝕜) (t : 𝕜) :
    HasDerivAt (fun s => eval (fun i => a i + s * v i) P)
      (eval (fun i => a i + t * v i) (complexPolynomialDirectional v P)) t := by
  apply hasDerivAt_eval_complex_curve P (fun s i => a i + s * v i) v t
  intro i
  simpa using (hasDerivAt_const t (a i)).fun_add ((hasDerivAt_id t).mul_const (v i))

end Calculus

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
