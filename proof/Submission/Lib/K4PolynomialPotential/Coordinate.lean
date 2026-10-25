import Mathlib

/-!
Adapted from: here:o062
Original source: here:o007,
Submission/Obl/k4_quadratic_slope_volume/PolynomialSlices.lean.
The general coordinate evaluation/differentiation and derivative-degree facts
are packaged here for polynomial potentials without an obligation import.
-/

namespace Submission.Lib.K4PolynomialPotential

open Set MeasureTheory

noncomputable def coordinatePolynomialHom {σ : Type*} [DecidableEq σ]
    (v : σ → ℝ) (i : σ) : MvPolynomial σ ℝ →+* Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = i then Polynomial.X else Polynomial.C (v j))

/-- Evaluation of a polynomial substitution commutes with evaluation of the
resulting univariate polynomial. -/
theorem eval_polynomial_substitution {σ : Type*} (P : MvPolynomial σ ℝ)
    (Q : σ → Polynomial ℝ) (w : ℝ) :
    (MvPolynomial.eval₂ Polynomial.C Q P).eval w =
      MvPolynomial.eval (fun i => (Q i).eval w) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q' hP hQ' => simp [MvPolynomial.eval₂_add, hP, hQ']
  | mul_X P j hP => simp [MvPolynomial.eval₂_mul, hP]

/-- The coordinate polynomial agrees with the original polynomial on its slice. -/
theorem eval_coordinatePolynomialHom {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (v : σ → ℝ) (i : σ) (w : ℝ) :
    (coordinatePolynomialHom v i P).eval w = MvPolynomial.eval (Function.update v i w) P := by
  rw [coordinatePolynomialHom, MvPolynomial.coe_eval₂Hom, eval_polynomial_substitution]
  apply congrArg (fun g : σ → ℝ => MvPolynomial.eval g P)
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

/-- Partial differentiation becomes ordinary differentiation on a coordinate slice. -/
theorem derivative_coordinatePolynomialHom {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (v : σ → ℝ) (i : σ) :
    (coordinatePolynomialHom v i P).derivative =
      coordinatePolynomialHom v i (MvPolynomial.pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [coordinatePolynomialHom]
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P j hP =>
    simp only [coordinatePolynomialHom, MvPolynomial.coe_eval₂Hom] at hP ⊢
    by_cases h : j = i
    · subst j
      simp [MvPolynomial.eval₂_mul, Polynomial.derivative_mul, hP, mul_comm]
    · simp [MvPolynomial.eval₂_mul, Polynomial.derivative_mul, hP, h, mul_comm]

theorem totalDegree_pderiv_le {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (i : σ) :
    (MvPolynomial.pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro m hm
  have hmne : (MvPolynomial.pderiv i P).coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hcoeff : P.coeff (m + Finsupp.single i 1) ≠ 0 := by
    rw [MvPolynomial.coeff_pderiv] at hmne
    exact (mul_ne_zero_iff.mp hmne).1
  have hdegree := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    simp
  rw [hsum] at hdegree
  omega


end Submission.Lib.K4PolynomialPotential
