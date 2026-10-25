/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/QuadraticExpansion.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/QuadraticExpansion.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SimpleSheets
import Submission.Obl.k4_algebraic_sheet_bound.LastVar
import Submission.Obl.k4_quadratic_atlas_normalization.Curvature

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MvPolynomial

private noncomputable abbrev lastVar (P : MvPolynomial (Fin 4) ℂ) :
    Polynomial (MvPolynomial (Fin 3) ℂ) :=
  Submission.Obl.k4_algebraic_sheet_bound.lastVar P

/-- The accepted last-variable representation intertwines the hidden partial
derivative and the ordinary polynomial derivative. -/
theorem lastVar_pderiv (P : MvPolynomial (Fin 4) ℂ) :
    lastVar (pderiv (3 : Fin 4) P) = (lastVar P).derivative := by
  let e : MvPolynomial (Fin 4) ℂ ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin 3) ℂ) :=
    (renameEquiv ℂ (finRotate 4)).trans (MvPolynomial.finSuccEquiv ℂ 3)
  have hX (i : Fin 4) : e (X i) =
      (Fin.snoc (fun j : Fin 3 => Polynomial.C (X j)) Polynomial.X :
        Fin 4 → Polynomial (MvPolynomial (Fin 3) ℂ)) i := by
    fin_cases i <;> simp [e, MvPolynomial.finSuccEquiv_apply] <;> rfl
  change e (pderiv (3 : Fin 4) P) = (e P).derivative
  induction P using MvPolynomial.induction_on with
  | C a => simp [e, MvPolynomial.finSuccEquiv_apply]
  | add P Q hP hQ =>
    simpa only [map_add, Polynomial.derivative_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P j hP =>
    simp only [pderiv_mul, map_add, map_mul, hP, Polynomial.derivative_mul, hX]
    fin_cases j <;> simp [e, MvPolynomial.finSuccEquiv_apply, Fin.snoc, mul_comm, add_comm]

/-- The degree in the hidden variable is bounded by the original total degree. -/
theorem natDegree_lastVar_le (P : MvPolynomial (Fin 4) ℂ) :
    (lastVar P).natDegree ≤ P.totalDegree := by
  unfold lastVar Submission.Obl.k4_algebraic_sheet_bound.lastVar
  rw [natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree _ _).trans (totalDegree_rename_le _ _)

/-- Evaluate a polynomial after complexifying its real coefficients and inputs. -/
theorem eval_complexification {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (z : Fin n → ℝ) :
    eval (fun i => (z i : ℂ)) (P.map (algebraMap ℝ ℂ)) = (eval z P : ℂ) := by
  rw [eval_map]
  simpa only [Complex.coe_algebraMap, Function.comp_def] using
    (eval₂_comp (algebraMap ℝ ℂ) z P).symm

theorem eval_complexification_snoc (P : MvPolynomial (Fin 4) ℝ) (z : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc (fun i : Fin 3 => (z i : ℂ)) (w : ℂ)) (P.map (algebraMap ℝ ℂ)) =
      (eval (Fin.snoc z w) P : ℂ) := by
  have heq : (fun i : Fin 4 => ((Fin.snoc z w : Fin 4 → ℝ) i : ℂ)) =
      Fin.snoc (fun i : Fin 3 => (z i : ℂ)) (w : ℂ) :=
    Fin.comp_snoc (fun r : ℝ => (r : ℂ)) z w
  rw [← heq]
  exact eval_complexification P _

theorem eval_complexification_snoc_zero (P : MvPolynomial (Fin 4) ℝ) (z : Fin 3 → ℝ) :
    eval (Fin.snoc (fun i : Fin 3 => (z i : ℂ)) (0 : ℂ)) (P.map (algebraMap ℝ ℂ)) =
      (eval (Fin.snoc z 0) P : ℂ) := by
  simpa only [Complex.ofReal_zero] using eval_complexification_snoc P z 0

/-- A quadratic univariate polynomial is determined by its value, first
derivative, and second derivative at zero. -/
theorem eval_quadratic_zero (p : Polynomial ℂ) (hp : p.natDegree ≤ 2) (w : ℂ) :
    p.eval w = p.eval 0 + p.derivative.eval 0 * w +
      p.derivative.derivative.eval 0 / 2 * w ^ 2 := by
  rw [Polynomial.eval_eq_sum_range' (show p.natDegree < 3 by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, mul_one, pow_one, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative]
  ring

/-- The hidden derivative is affine, in the same zero-based coordinates. -/
theorem eval_quadratic_derivative (p : Polynomial ℂ) (hp : p.natDegree ≤ 2) (w : ℂ) :
    p.derivative.eval w = p.derivative.eval 0 + p.derivative.derivative.eval 0 * w := by
  have heq : p = Polynomial.C (p.eval 0) + Polynomial.C (p.derivative.eval 0) * Polynomial.X +
      Polynomial.C (p.derivative.derivative.eval 0 / 2) * Polynomial.X ^ 2 := by
    apply Polynomial.funext
    intro v
    simpa using eval_quadratic_zero p hp v
  conv_lhs => rw [heq]
  simp
  ring

/-- The complexified hidden-coordinate quadratic has the original real constant
curvature. This uses the accepted constant-curvature identity from o115. -/
theorem eval_hidden_quadratic (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℂ) (w : ℂ) :
    eval (Fin.snoc z w) (P.map (algebraMap ℝ ℂ)) =
      eval (Fin.snoc z 0) (P.map (algebraMap ℝ ℂ)) +
      eval (Fin.snoc z 0) ((pderiv (3 : Fin 4) P).map (algebraMap ℝ ℂ)) * w +
      (Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) : ℂ) / 2 * w ^ 2 := by
  let Q := P.map (algebraMap ℝ ℂ)
  let q := (lastVar Q).map (eval z)
  have hQ : Q.totalDegree ≤ P.totalDegree := by
    classical
    exact Finset.sup_mono (support_map_subset (f := algebraMap ℝ ℂ) P)
  have hq : q.natDegree ≤ 2 :=
    (Polynomial.natDegree_map_le).trans ((natDegree_lastVar_le Q).trans (hQ.trans hP))
  have hcurv : pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q) =
      C (Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) : ℂ) := by
    simp only [Q, pderiv_map,
      Submission.Obl.k4_quadratic_atlas_normalization.second_pderiv_eq_curvature P hP,
      map_C, Complex.coe_algebraMap]
  have heval := eval_quadratic_zero q hq w
  simpa only [q, Polynomial.derivative_map, ← lastVar_pderiv, hcurv,
    ← Submission.Obl.k4_algebraic_sheet_bound.eval_snoc_eq_lastVar, Q, pderiv_map,
    Submission.Obl.k4_quadratic_atlas_normalization.second_pderiv_eq_curvature P hP,
    map_C, eval_C, Complex.coe_algebraMap] using heval

theorem eval_hidden_derivative (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℂ) (w : ℂ) :
    eval (Fin.snoc z w) ((pderiv (3 : Fin 4) P).map (algebraMap ℝ ℂ)) =
      eval (Fin.snoc z 0) ((pderiv (3 : Fin 4) P).map (algebraMap ℝ ℂ)) +
      (Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) : ℂ) * w := by
  let Q := P.map (algebraMap ℝ ℂ)
  let q := (lastVar Q).map (eval z)
  have hQ : Q.totalDegree ≤ P.totalDegree := by
    classical
    exact Finset.sup_mono (support_map_subset (f := algebraMap ℝ ℂ) P)
  have hq : q.natDegree ≤ 2 :=
    Polynomial.natDegree_map_le.trans ((natDegree_lastVar_le Q).trans (hQ.trans hP))
  have heval := eval_quadratic_derivative q hq w
  simpa only [q, Polynomial.derivative_map, ← lastVar_pderiv,
    ← Submission.Obl.k4_algebraic_sheet_bound.eval_snoc_eq_lastVar, Q, pderiv_map,
    Submission.Obl.k4_quadratic_atlas_normalization.second_pderiv_eq_curvature P hP,
    map_C, eval_C, Complex.coe_algebraMap] using heval

theorem eval_real_hidden_quadratic (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc z w) P = eval (Fin.snoc z 0) P +
      eval (Fin.snoc z 0) (pderiv (3 : Fin 4) P) * w +
      Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) / 2 * w ^ 2 := by
  have h := eval_hidden_quadratic P hP (fun i : Fin 3 => (z i : ℂ)) (w : ℂ)
  rw [eval_complexification_snoc P z w, eval_complexification_snoc_zero P z,
    eval_complexification_snoc_zero (pderiv (3 : Fin 4) P) z] at h
  exact_mod_cast h

theorem eval_real_hidden_derivative (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc z w) (pderiv (3 : Fin 4) P) =
      eval (Fin.snoc z 0) (pderiv (3 : Fin 4) P) +
      Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) * w := by
  have h := eval_hidden_derivative P hP (fun i : Fin 3 => (z i : ℂ)) (w : ℂ)
  rw [eval_complexification_snoc (pderiv (3 : Fin 4) P) z w,
    eval_complexification_snoc_zero (pderiv (3 : Fin 4) P) z] at h
  exact_mod_cast h

/-- Real-coefficient complex polynomial tests are holomorphic at hidden value zero. -/
theorem differentiable_hidden_zero (P : MvPolynomial (Fin 4) ℂ) :
    Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin 3) =>
      eval (Fin.snoc (fun i : Fin 3 => z i) 0) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    simp only [eval_add]
    convert hP.add hQ using 1
  | mul_X P j hP =>
    have hj : Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin 3) =>
        (Fin.snoc (fun i : Fin 3 => z i) 0 : Fin 4 → ℂ) j) := by
      fin_cases j
      · convert (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiable using 1 <;> rfl
      · convert (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).differentiable using 1 <;> rfl
      · convert (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable using 1 <;> rfl
      · exact differentiable_const 0
    simp only [eval_mul, eval_X]
    convert hP.mul hj using 1

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
