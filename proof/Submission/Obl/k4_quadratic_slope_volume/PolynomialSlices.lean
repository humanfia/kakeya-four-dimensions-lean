import Mathlib
import Submission.Lib.K4QuadraticSublevel
import Submission.Lib.K4GoodTimes

namespace Submission.Obl.k4_quadratic_slope_volume

open Set MeasureTheory

/-- Substituting affine univariate polynomials cannot increase total degree. -/
theorem natDegree_eval₂_affine_le {σ : Type*} (P : MvPolynomial σ ℝ)
    (Q : σ → Polynomial ℝ) (hQ : ∀ i, (Q i).natDegree ≤ 1) :
    (MvPolynomial.eval₂ Polynomial.C Q P).natDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [MvPolynomial.eval₂_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [MvPolynomial.eval₂_monomial]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  calc
    (m.prod fun i e => Q i ^ e).natDegree ≤
        m.sum (fun i e => (Q i ^ e).natDegree) := Polynomial.natDegree_prod_le _ _
    _ ≤ m.sum (fun _ e => e) := by
      apply Finsupp.sum_le_sum
      intro i hi
      exact Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (m i) (hQ i))
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hm

/-- Freeze every coordinate but `i`, retaining the `i`th coordinate as a
univariate indeterminate. -/
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

/-- The regular sublevel set on any coordinate line of a quadratic has bounded
one-dimensional measure. -/
theorem volume_quadratic_coordinate_sublevel {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) (ε β : ℝ) (hε : 0 ≤ ε) (hβ : 0 < β) :
    volume {w : ℝ | |MvPolynomial.eval (Function.update v i w) P| ≤ ε ∧
      β ≤ |MvPolynomial.eval (Function.update v i w) (MvPolynomial.pderiv i P)|} ≤
      ENNReal.ofReal (4 * ε / β) := by
  have hdegree : (coordinatePolynomialHom v i P).natDegree ≤ 2 := by
    apply (natDegree_eval₂_affine_le P _ ?_).trans hP
    intro j
    split_ifs <;> simp
  have h := Submission.Lib.K4QuadraticSublevel.volume_quadratic_sublevel
    (coordinatePolynomialHom v i P) hdegree hε hβ
  simpa only [derivative_coordinatePolynomialHom, eval_coordinatePolynomialHom] using h

/-- A partial derivative lowers total degree by at least one. -/
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

/-- Restrict a spacetime polynomial to a spatial trajectory. -/
noncomputable def linePolynomial (P : MvPolynomial (Fin 4) ℝ)
    (b s : EuclideanSpace ℝ (Fin 3)) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    ![Polynomial.X, Polynomial.C (b 0) + Polynomial.C (s 0) * Polynomial.X,
      Polynomial.C (b 1) + Polynomial.C (s 1) * Polynomial.X,
      Polynomial.C (b 2) + Polynomial.C (s 2) * Polynomial.X] P

theorem eval_linePolynomial (P : MvPolynomial (Fin 4) ℝ)
    (b s : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    (linePolynomial P b s).eval t =
      MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] P := by
  rw [linePolynomial, eval_polynomial_substitution]
  apply congrArg (fun v : Fin 4 → ℝ => MvPolynomial.eval v P)
  funext i
  fin_cases i <;> dsimp <;> simp only [Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring

theorem natDegree_linePolynomial_le (P : MvPolynomial (Fin 4) ℝ)
    (b s : EuclideanSpace ℝ (Fin 3)) :
    (linePolynomial P b s).natDegree ≤ P.totalDegree := by
  apply natDegree_eval₂_affine_le
  intro i
  have h (b s : ℝ) : (Polynomial.C b + Polynomial.C s * Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  fin_cases i <;> dsimp
  · simp
  · exact h _ _
  · exact h _ _
  · exact h _ _

/-- The native derivative of a quadratic is affine along each trajectory. -/
theorem exists_affine_native_derivative (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (b s : EuclideanSpace ℝ (Fin 3)) :
    ∃ m d : ℝ, ∀ t : ℝ,
      MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2]
        (MvPolynomial.pderiv (3 : Fin 4) P) = m * t + d := by
  let Q := linePolynomial (MvPolynomial.pderiv (3 : Fin 4) P) b s
  have hdegree : Q.natDegree ≤ 1 := by
    apply (natDegree_linePolynomial_le _ _ _).trans
    exact (totalDegree_pderiv_le P _).trans (by omega)
  obtain ⟨m, d, hQ⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hdegree
  refine ⟨m, d, fun t => ?_⟩
  rw [← eval_linePolynomial]
  change Q.eval t = _
  rw [hQ]
  simp

/-- The good-time estimate expressed in the exact polynomial coordinates of the
slope-volume theorem. -/
theorem volume_native_derivative_good_times (A : Matrix (Fin 3) (Fin 3) ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (b s : EuclideanSpace ℝ (Fin 3)) (t₀ q K : ℝ) (hq : 0 < q) (hK : 0 < K)
    (hlarge : ∃ t ∈ Icc t₀ (t₀ + q), K⁻¹ ≤
      |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|) :
    ENNReal.ofReal (q / 2) ≤ volume {t : ℝ | t ∈ Icc t₀ (t₀ + q) ∧
      (q / 24) ^ 3 ≤ |(A + Matrix.scalar (Fin 3) t).det| ∧
      K⁻¹ / 16 ≤ |MvPolynomial.eval
        ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|} := by
  obtain ⟨m, d, heval⟩ := exists_affine_native_derivative P hP b s
  simp_rw [heval] at hlarge ⊢
  exact Submission.Lib.K4GoodTimes.volume_det_affine_good_times A m d t₀ q K hq hK hlarge

end Submission.Obl.k4_quadratic_slope_volume
