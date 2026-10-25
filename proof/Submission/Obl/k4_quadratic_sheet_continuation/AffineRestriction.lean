import Submission.Obl.k4_quadratic_sheet_continuation.Smooth

/-!
# Affine restriction in the base variables

From session x0449 of this LOT obligation, branch x0449, commit 58b4584.

The dependent coordinates remain indeterminates. Simplicity of an original
sheet prevents a restricted equation from becoming the zero polynomial.
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open MvPolynomial

abbrev Space (n : ℕ) := EuclideanSpace ℂ (Fin n)

def evaluation {n m : ℕ}
    (f : Fin m → Space n → ℂ) (Q : MvPolynomial (Fin (n + m)) ℂ)
    (z : Space n) : ℂ :=
  MvPolynomial.eval
    (Fin.append (fun j : Fin n => z j) (fun i : Fin m => f i z)) Q

noncomputable def lineVariables {n m : ℕ} (p v : Space n) :
    Fin (n + m) → MvPolynomial (Fin (1 + m)) ℂ :=
  Fin.addCases
    (fun j => C (p j) + X (Fin.castAdd m (0 : Fin 1)) * C (v j))
    (fun i => X (Fin.natAdd 1 i))

noncomputable def restrictLine {n m : ℕ} (p v : Space n) :
    MvPolynomial (Fin (n + m)) ℂ →+* MvPolynomial (Fin (1 + m)) ℂ :=
  eval₂Hom C (lineVariables p v)

@[simp] theorem restrictLine_C {n m : ℕ} (p v : Space n) (a : ℂ) :
    restrictLine (m := m) p v (C a) = C a := by
  simp [restrictLine]

@[simp] theorem restrictLine_X {n m : ℕ} (p v : Space n) (i : Fin (n + m)) :
    restrictLine p v (X i) = lineVariables p v i := by
  simp [restrictLine]

/-- Adapted from this LOT tree, o029, file
`Submission/Obl/k4_bounded_sign_choice/PolynomialFamily.lean`,
`totalDegree_eval₂_le`; generalized from real to complex coefficients. -/
theorem totalDegree_affine_substitution {ι κ : Type}
    (f : ι → MvPolynomial κ ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial ι ℂ) :
    (eval₂ C f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [eval₂_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [eval₂_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ i ∈ d.support, ((f i) ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ P.totalDegree := le_totalDegree hd

theorem totalDegree_restrictLine_le {n m : ℕ} (p v : Space n)
    (P : MvPolynomial (Fin (n + m)) ℂ) :
    (restrictLine p v P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_affine_substitution
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [lineVariables, Fin.addCases_left]
    refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    simpa using totalDegree_mul
      (X (Fin.castAdd m (0 : Fin 1)) : MvPolynomial (Fin (1 + m)) ℂ) (C (v j))
  · simp [lineVariables]

theorem eval_restrictLine {n m : ℕ} (p v : Space n)
    (P : MvPolynomial (Fin (n + m)) ℂ) (t : ℂ) (w : Fin m → ℂ) :
    eval (Fin.append (fun _ : Fin 1 => t) w) (restrictLine p v P) =
      eval (Fin.append (fun j : Fin n => (p + t • v) j) w) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, restrictLine_X, eval_mul, eval_X, hP]
    congr 1
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [lineVariables, PiLp.add_apply, PiLp.smul_apply]
    · simp [lineVariables]

theorem eval_restrictLine_snoc {n : ℕ} (p v : Space n)
    (P : MvPolynomial (Fin (n + 1)) ℂ) (t w : ℂ) :
    eval (Fin.snoc (fun _ : Fin 1 => t) w) (restrictLine p v P) =
      eval (Fin.snoc (fun j : Fin n => (p + t • v) j) w) P := by
  simpa only [Fin.append_right_eq_snoc] using
    eval_restrictLine p v P t (fun _ : Fin 1 => w)

theorem eval_pderiv_restrictLine_snoc {n : ℕ} (p v : Space n)
    (P : MvPolynomial (Fin (n + 1)) ℂ) (t w : ℂ) :
    eval (Fin.snoc (fun _ : Fin 1 => t) w)
        (pderiv (Fin.last 1) (restrictLine p v P)) =
      eval (Fin.snoc (fun j : Fin n => (p + t • v) j) w)
        (pderiv (Fin.last n) P) := by
  have hfun :
      (fun u : ℂ => eval (Fin.snoc (fun _ : Fin 1 => t) u) (restrictLine p v P)) =
      (fun u : ℂ => eval (Fin.snoc (fun j : Fin n => (p + t • v) j) u) P) :=
    funext (eval_restrictLine_snoc p v P t)
  have h₁ := hasDerivAt_eval_snoc (restrictLine p v P) (fun _ => t) w
  rw [hfun] at h₁
  exact h₁.unique (hasDerivAt_eval_snoc P (fun j => (p + t • v) j) w)

theorem restrictLine_ne_zero_of_simple {n : ℕ} (p v : Space n)
    (P : MvPolynomial (Fin (n + 1)) ℂ) (w : ℂ)
    (h : eval (Fin.snoc (fun j : Fin n => p j) w)
      (pderiv (Fin.last n) P) ≠ 0) : restrictLine p v P ≠ 0 := by
  intro hz
  have heq := eval_pderiv_restrictLine_snoc p v P 0 w
  simp only [hz, map_zero, zero_smul, add_zero] at heq
  exact h heq.symm

end Submission.Obl.k4_quadratic_sheet_continuation
