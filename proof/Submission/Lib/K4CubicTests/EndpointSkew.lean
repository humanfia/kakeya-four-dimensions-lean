/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

open MvPolynomial

namespace Submission.Lib.K4CubicTests

/-- Entry bounds multiply with only the number of contracted indices. -/
theorem matrix_mul_entry_abs_le {ι κ τ : Type*} [Fintype κ]
    (M : Matrix ι κ ℝ) (N : Matrix κ τ ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hM : ∀ i k, |M i k| ≤ a) (hN : ∀ k j, |N k j| ≤ b) (i : ι) (j : τ) :
    |(M * N) i j| ≤ (Fintype.card κ : ℝ) * a * b := by
  classical
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k : κ, |M i k * N k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : κ, a * b := Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_mul (hM i k) (hN k j) (abs_nonneg _) ha
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- A small residual cross Hessian forces a small skew part after
transporting between two bases. The within-first-basis Hessian is symmetric. -/
theorem matrix_skew_abs_le_of_cross_residual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B Ai Bi D S E : Matrix ι ι ℝ)
    (hA : A * Ai = 1) (hB : B * Bi = 1) (hS : S.transpose = S)
    (hE : E = A.transpose * D.transpose * B - S * Ai * B)
    (Ua Ub η : ℝ) (hUa : 0 ≤ Ua) (hUb : 0 ≤ Ub) (hη : 0 ≤ η)
    (hAi : ∀ i j, |Ai i j| ≤ Ua) (hBi : ∀ i j, |Bi i j| ≤ Ub)
    (hsmall : ∀ i j, |E i j| ≤ η) (i j : ι) :
    |D i j - D j i| ≤ 2 * (Fintype.card ι : ℝ)^2 * Ua * Ub * η := by
  let W := Ai.transpose * E * Bi
  have hW : W = D.transpose - Ai.transpose * S * Ai := by
    calc
      W = (Ai.transpose * A.transpose) * D.transpose * (B * Bi) -
          Ai.transpose * S * Ai * (B * Bi) := by dsimp [W]; rw [hE]; noncomm_ring
      _ = _ := by rw [← Matrix.transpose_mul, hA, hB]; simp
  have hsym : (Ai.transpose * S * Ai).transpose = Ai.transpose * S * Ai := by
    simp [Matrix.transpose_mul, hS, Matrix.mul_assoc]
  have hskew : D.transpose - D = W - W.transpose := by
    rw [hW, Matrix.transpose_sub, Matrix.transpose_transpose, hsym]
    abel
  have hAiE : ∀ k l, |(Ai.transpose * E) k l| ≤ (Fintype.card ι : ℝ) * Ua * η :=
    matrix_mul_entry_abs_le Ai.transpose E Ua η hUa hη (fun i j => hAi j i) hsmall
  have hentry : ∀ k l, |W k l| ≤ (Fintype.card ι : ℝ)^2 * Ua * Ub * η := by
    intro k l
    have h := matrix_mul_entry_abs_le (Ai.transpose * E) Bi
      ((Fintype.card ι : ℝ) * Ua * η) Ub (by positivity) hUb hAiE hBi k l
    exact h.trans_eq (by ring)
  have heq := congrArg (fun M : Matrix ι ι ℝ => M j i) hskew
  change D i j - D j i = W j i - W i j at heq
  rw [heq]
  calc
    _ ≤ |W j i| + |W i j| := abs_sub _ _
    _ ≤ _ := by linarith [hentry j i, hentry i j]

/-- Coordinate derivatives commute, in any variable type. -/
theorem polynomial_pderiv_comm_all {σ : Type*} (F : MvPolynomial σ ℝ) (i j : σ) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  classical
  by_cases hij : i = j
  · subst j; rfl
  ext m
  simp [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij,
    add_assoc, add_comm, add_left_comm] <;> ring

/-- Height derivative in a direction that cancels a base displacement
using the first basis. Its determinant multiple is an endpoint minor. -/
noncomputable def endpointKernelPolynomial {σ ι : Type*} [Fintype ι]
    (H : MvPolynomial σ ℝ) (Ai B : Matrix ι ι ℝ) (left right : ι → σ) (j : ι) :
    MvPolynomial σ ℝ :=
  pderiv (right j) H - ∑ i : ι, C ((Ai * B) i j) * pderiv (left i) H

/-- Small coefficients of every base-cancelling height derivative force a
small skew field derivative, using its actual endpoint cross Hessian. -/
theorem endpoint_skew_abs_le_of_kernel_coeff {σ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (H : MvPolynomial σ ℝ) (left right : ι → σ)
    (A B Ai Bi D : Matrix ι ι ℝ)
    (hA : A * Ai = 1) (hB : B * Bi = 1)
    (hcross : ∀ i j,
      MvPolynomial.eval (fun _ => 0) (pderiv (left i) (pderiv (right j) H)) =
        (A.transpose * D.transpose * B) i j)
    (Ua Ub η : ℝ) (hUa : 0 ≤ Ua) (hUb : 0 ≤ Ub) (hη : 0 ≤ η)
    (hAi : ∀ i j, |Ai i j| ≤ Ua) (hBi : ∀ i j, |Bi i j| ≤ Ub)
    (hcoeff : ∀ j m, |(endpointKernelPolynomial H Ai B left right j).coeff m| ≤ η)
    (i j : ι) :
    |D i j - D j i| ≤ 2 * (Fintype.card ι : ℝ)^2 * Ua * Ub * η := by
  classical
  let S : Matrix ι ι ℝ := fun k l =>
    MvPolynomial.eval (fun _ => 0) (pderiv (left k) (pderiv (left l) H))
  let E : Matrix ι ι ℝ := fun k l => MvPolynomial.eval (fun _ => 0)
    (pderiv (left k) (endpointKernelPolynomial H Ai B left right l))
  have hS : S.transpose = S := by
    ext k l
    change MvPolynomial.eval (fun _ => 0) (pderiv (left l) (pderiv (left k) H)) = _
    rw [polynomial_pderiv_comm_all H (left l) (left k)]
  have hE : E = A.transpose * D.transpose * B - S * Ai * B := by
    ext k l
    rw [Matrix.mul_assoc S Ai B]
    change MvPolynomial.eval (fun _ => 0)
      (pderiv (left k) (endpointKernelPolynomial H Ai B left right l)) = _
    simp only [endpointKernelPolynomial, map_sub, map_sum, pderiv_C_mul,
      map_mul, eval_C, hcross, Matrix.sub_apply]
    congr 1
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  have hsmall : ∀ k l, |E k l| ≤ η := by
    intro k l
    have hev (Q : MvPolynomial σ ℝ) : MvPolynomial.eval (fun _ => 0) Q = Q.coeff 0 := by
      rw [eval_zero']; rfl
    simpa only [E, hev, coeff_pderiv, zero_add, Finsupp.coe_zero, Pi.zero_apply,
      Nat.cast_zero, zero_add, mul_one] using hcoeff l (Finsupp.single (left k) 1)
  exact matrix_skew_abs_le_of_cross_residual A B Ai Bi D S E hA hB hS hE
    Ua Ub η hUa hUb hη hAi hBi hsmall i j

/-- The determinant multiple of a base-cancelling height derivative. -/
noncomputable def endpointMinorPolynomial {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : MvPolynomial σ ℝ) (A Ai B : Matrix ι ι ℝ) (left right : ι → σ) (j : ι) :
    MvPolynomial σ ℝ :=
  C A.det * endpointKernelPolynomial H Ai B left right j

/-- This polynomial is the actual block Jacobian minor of the endpoint
with base columns from `A` and the selected column of `B`. -/
theorem eval_endpointMinorPolynomial_eq_det {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : MvPolynomial σ ℝ) (A Ai B : Matrix ι ι ℝ) (hA : A * Ai = 1)
    (left right : ι → σ) (j : ι) (δ : σ → ℝ) :
    MvPolynomial.eval δ (endpointMinorPolynomial H A Ai B left right j) =
      (Matrix.fromBlocks A (Matrix.of (fun a (_ : Unit) => B a j))
        (Matrix.of (fun (_ : Unit) i => MvPolynomial.eval δ (pderiv (left i) H)))
        (Matrix.of (fun (_ _ : Unit) => MvPolynomial.eval δ (pderiv (right j) H)))).det := by
  letI : Invertible A := invertibleOfRightInverse A Ai hA
  have hinv : ⅟A = Ai := invOf_eq_right_inv hA
  have hm :
      ((Matrix.of (fun (_ : Unit) i => MvPolynomial.eval δ (pderiv (left i) H))) * Ai *
        (Matrix.of (fun a (_ : Unit) => B a j))) () () =
      ∑ i : ι, (Ai * B) i j * MvPolynomial.eval δ (pderiv (left i) H) := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [Matrix.det_fromBlocks₁₁, hinv, Matrix.det_unique (n := Unit)]
  change _ = A.det * (MvPolynomial.eval δ (pderiv (right j) H) - _)
  rw [hm]
  simp only [endpointMinorPolynomial, endpointKernelPolynomial, map_mul, eval_C,
    map_sub, map_sum]

/-- Any skew entry above the quantitative threshold forces a large
coefficient in a base-cancelling endpoint derivative. -/
theorem exists_large_endpointKernelPolynomial_coeff {σ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (H : MvPolynomial σ ℝ) (left right : ι → σ)
    (A B Ai Bi D : Matrix ι ι ℝ)
    (hA : A * Ai = 1) (hB : B * Bi = 1)
    (hcross : ∀ i j,
      MvPolynomial.eval (fun _ => 0) (pderiv (left i) (pderiv (right j) H)) =
        (A.transpose * D.transpose * B) i j)
    (Ua Ub η : ℝ) (hUa : 0 ≤ Ua) (hUb : 0 ≤ Ub) (hη : 0 ≤ η)
    (hAi : ∀ i j, |Ai i j| ≤ Ua) (hBi : ∀ i j, |Bi i j| ≤ Ub)
    (hskew : ∃ i j, 2 * (Fintype.card ι : ℝ)^2 * Ua * Ub * η < |D i j - D j i|) :
    ∃ j m, η < |(endpointKernelPolynomial H Ai B left right j).coeff m| := by
  classical
  by_contra h
  push Not at h
  obtain ⟨i, j, hij⟩ := hskew
  exact (not_lt_of_ge (endpoint_skew_abs_le_of_kernel_coeff H left right
    A B Ai Bi D hA hB hcross Ua Ub η hUa hUb hη hAi hBi h i j)) hij

/-- A determinant floor turns a large kernel coefficient into a large
coefficient of an actual endpoint Jacobian minor. -/
theorem endpointMinorPolynomial_coeff_large_of_kernel {σ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (H : MvPolynomial σ ℝ) (A Ai B : Matrix ι ι ℝ) (left right : ι → σ)
    (j : ι) (m : σ →₀ ℕ) (d η : ℝ) (hd : 0 < d) (hdet : d ≤ |A.det|)
    (hlarge : η < |(endpointKernelPolynomial H Ai B left right j).coeff m|) :
    d * η < |(endpointMinorPolynomial H A Ai B left right j).coeff m| := by
  rw [endpointMinorPolynomial, coeff_C_mul, abs_mul]
  exact (mul_lt_mul_of_pos_left hlarge hd).trans_le
    (mul_le_mul_of_nonneg_right hdet (abs_nonneg _))

end Submission.Lib.K4CubicTests

