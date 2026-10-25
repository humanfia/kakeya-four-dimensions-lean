import Mathlib

/-!
# Polynomial algebra for lifting chart tests

Chart tests are lifted through a parent chart by an affine substitution of the
graph coordinates. This file proves the facts used about such substitutions:
the chain rule for `MvPolynomial.pderiv` under `MvPolynomial.bind₁`, the total
degree bound for substitutions of degree at most one, and an `ℓ¹` bound on
coefficients.
-/

namespace Submission.Lib.K4ChartLifting

open MvPolynomial

section ChainRule

variable {R : Type*} [CommRing R] {n m : ℕ}

/-- Chain rule for partial derivatives under substitution. -/
theorem pderiv_bind₁ (σ : Fin n → MvPolynomial (Fin m) R) (p : MvPolynomial (Fin n) R)
    (i : Fin m) :
    pderiv i (bind₁ σ p) = ∑ j, bind₁ σ (pderiv j p) * pderiv i (σ j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, bind₁_X_right, Derivation.leibniz, smul_eq_mul, hp, pderiv_X]
    simp only [map_add, map_mul, bind₁_X_right]
    rw [Finset.sum_congr rfl (fun x _ => add_mul _ _ _), Finset.sum_add_distrib]
    have h1 : ∑ x : Fin n, (bind₁ σ) p *
        (bind₁ σ) ((Pi.single x (1 : MvPolynomial (Fin n) R) : Fin n → MvPolynomial (Fin n) R) k)
        * (pderiv i) (σ x) = (bind₁ σ) p * (pderiv i) (σ k) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    rw [h1, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- If the substituted polynomial in the coordinate `i` is `X i` and no other
substituted polynomial depends on `X i`, then `pderiv i` commutes with the
substitution. -/
theorem pderiv_bind₁_of_diagonal (σ : Fin n → MvPolynomial (Fin n) R) (i : Fin n)
    (hi : pderiv i (σ i) = 1) (hj : ∀ j, j ≠ i → pderiv i (σ j) = 0)
    (p : MvPolynomial (Fin n) R) :
    pderiv i (bind₁ σ p) = bind₁ σ (pderiv i p) := by
  rw [pderiv_bind₁, Finset.sum_eq_single i]
  · rw [hi, mul_one]
  · intro j _ hji
    rw [hj j hji, mul_zero]
  · simp

/-- Substituting polynomials of degree at most one does not raise total degree. -/
theorem totalDegree_bind₁_le_of_le_one (σ : Fin n → MvPolynomial (Fin m) R)
    (hσ : ∀ j, (σ j).totalDegree ≤ 1) (p : MvPolynomial (Fin n) R) :
    (bind₁ σ p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ d.support, (σ i ^ d i).totalDegree
      ≤ ∑ i ∈ d.support, d i := by
        apply Finset.sum_le_sum
        intro i _
        refine (totalDegree_pow _ _).trans ?_
        simpa using Nat.mul_le_mul_left (d i) (hσ i)
    _ = d.sum (fun _ e => e) := rfl
    _ ≤ p.totalDegree := le_totalDegree hd

end ChainRule

section L1

variable {σ : Type*}

/-- The `ℓ¹` norm of the coefficients of a real polynomial. -/
noncomputable def coeffL1 (p : MvPolynomial σ ℝ) : ℝ := ∑ m ∈ p.support, |p.coeff m|

theorem coeffL1_nonneg (p : MvPolynomial σ ℝ) : 0 ≤ coeffL1 p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_coeff_le_coeffL1 (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |p.coeff m| ≤ coeffL1 p := by
  classical
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun m => |p.coeff m|) (fun _ _ => abs_nonneg _) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]
    exact coeffL1_nonneg p

theorem coeffL1_eq_sum_of_support_subset (p : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ))
    (hs : p.support ⊆ s) : coeffL1 p = ∑ m ∈ s, |p.coeff m| := by
  classical
  unfold coeffL1
  apply Finset.sum_subset hs
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]

theorem coeffL1_add_le (p q : MvPolynomial σ ℝ) :
    coeffL1 (p + q) ≤ coeffL1 p + coeffL1 q := by
  classical
  have h1 := coeffL1_eq_sum_of_support_subset (p + q) (p.support ∪ q.support)
    MvPolynomial.support_add
  have h2 := coeffL1_eq_sum_of_support_subset p (p.support ∪ q.support)
    Finset.subset_union_left
  have h3 := coeffL1_eq_sum_of_support_subset q (p.support ∪ q.support)
    Finset.subset_union_right
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m _
  have : (p + q).coeff m = p.coeff m + q.coeff m := by simp
  rw [this]
  exact abs_add_le _ _

theorem coeffL1_zero : coeffL1 (0 : MvPolynomial σ ℝ) = 0 := by simp [coeffL1]

theorem coeffL1_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    coeffL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffL1_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (coeffL1_add_le _ _).trans (add_le_add le_rfl ih)

theorem coeffL1_monomial (m : σ →₀ ℕ) (c : ℝ) : coeffL1 (monomial m c) = |c| := by
  classical
  by_cases hc : c = 0
  · simp [hc, coeffL1_zero]
  · simp [coeffL1, MvPolynomial.support_monomial, hc]

theorem coeffL1_mul_le (p q : MvPolynomial σ ℝ) :
    coeffL1 (p * q) ≤ coeffL1 p * coeffL1 q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum, Finset.sum_mul_sum]
  refine (coeffL1_sum_le _ _).trans ?_
  rw [coeffL1, coeffL1, Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro m _
  refine (coeffL1_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro m' _
  rw [MvPolynomial.monomial_mul_monomial, coeffL1_monomial, abs_mul]

theorem coeffL1_C (c : ℝ) : coeffL1 (C c : MvPolynomial σ ℝ) = |c| := by
  rw [← MvPolynomial.monomial_zero', coeffL1_monomial]

theorem coeffL1_one : coeffL1 (1 : MvPolynomial σ ℝ) = 1 := by
  rw [← MvPolynomial.C_1, coeffL1_C, abs_one]

theorem coeffL1_smul (c : ℝ) (p : MvPolynomial σ ℝ) :
    coeffL1 (c • p) ≤ |c| * coeffL1 p := by
  rw [MvPolynomial.smul_eq_C_mul]
  exact (coeffL1_mul_le _ _).trans (by rw [coeffL1_C])

theorem coeffL1_pow_le (p : MvPolynomial σ ℝ) (k : ℕ) :
    coeffL1 (p ^ k) ≤ coeffL1 p ^ k := by
  induction k with
  | zero => simp [coeffL1_one]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (coeffL1_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (coeffL1_nonneg _))

theorem coeffL1_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    coeffL1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, coeffL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffL1_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (coeffL1_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (coeffL1_nonneg _))


theorem coeffL1_X (i : σ) : coeffL1 (X i : MvPolynomial σ ℝ) = 1 := by
  rw [X, coeffL1_monomial, abs_one]

theorem coeffL1_neg (p : MvPolynomial σ ℝ) : coeffL1 (-p) = coeffL1 p := by
  simp [coeffL1, MvPolynomial.support_neg]

theorem coeffL1_sub_le (p q : MvPolynomial σ ℝ) :
    coeffL1 (p - q) ≤ coeffL1 p + coeffL1 q := by
  rw [sub_eq_add_neg, ← coeffL1_neg q]
  exact coeffL1_add_le _ _

theorem coeffL1_C_mul_le (a : ℝ) (p : MvPolynomial σ ℝ) :
    coeffL1 (C a * p) ≤ |a| * coeffL1 p :=
  (coeffL1_mul_le _ _).trans (by rw [coeffL1_C])

theorem coeffL1_mul_C_le (a : ℝ) (p : MvPolynomial σ ℝ) :
    coeffL1 (p * C a) ≤ coeffL1 p * |a| :=
  (coeffL1_mul_le _ _).trans (by rw [coeffL1_C])

/-- `ℓ¹` bound for a substitution: every substituted polynomial has `ℓ¹` norm at
most `S ≥ 1`. -/
theorem coeffL1_bind₁_le {τ : Type*} (f : σ → MvPolynomial τ ℝ) (S : ℝ) (hS : 1 ≤ S)
    (hf : ∀ i, coeffL1 (f i) ≤ S) (p : MvPolynomial σ ℝ) :
    coeffL1 (bind₁ f p) ≤ coeffL1 p * S ^ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (coeffL1_sum_le _ _).trans ?_
  rw [coeffL1, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  rw [bind₁_monomial]
  refine (coeffL1_mul_le _ _).trans ?_
  rw [coeffL1_C]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine (coeffL1_prod_le _ _).trans ?_
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  calc ∏ i ∈ d.support, coeffL1 (f i ^ d i)
      ≤ ∏ i ∈ d.support, S ^ d i := by
        apply Finset.prod_le_prod₀ (fun i _ => coeffL1_nonneg _)
        intro i _
        exact (coeffL1_pow_le _ _).trans
          (pow_le_pow_left₀ (coeffL1_nonneg _) (hf i) _)
    _ = S ^ (d.sum fun _ e => e) := by
        rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ S ^ p.totalDegree := pow_le_pow_right₀ hS (le_totalDegree hd)

/-- Monomials of a polynomial of total degree at most `D` in `n` variables number
at most `(D + 1) ^ n`. -/
theorem card_support_le {n D : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ D) :
    p.support.card ≤ (D + 1) ^ n := by
  classical
  have hinj : Set.InjOn (fun m : Fin n →₀ ℕ => fun i : Fin n => (m i : ℕ)) p.support := by
    intro a _ b _ hab
    ext i
    exact congrFun hab i
  have hmaps : ∀ m ∈ p.support, (fun i : Fin n => (m i : ℕ)) ∈
      (Fintype.piFinset fun _ : Fin n => Finset.range (D + 1)) := by
    intro m hm
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have h1 : m i ≤ m.sum (fun _ e => e) := by
      by_cases hi : i ∈ m.support
      · exact Finset.single_le_sum (f := fun j => m j) (fun _ _ => Nat.zero_le _) hi
      · simp [Finsupp.notMem_support_iff.mp hi]
    have h2 := le_totalDegree hm
    omega
  calc p.support.card ≤ (Fintype.piFinset fun _ : Fin n => Finset.range (D + 1)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (D + 1) ^ n := by simp

/-- The `ℓ¹` norm is at most the number of monomials times a coefficient bound. -/
theorem coeffL1_le_of_coeff_le {n D : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ D) (A : ℝ) (hA : ∀ m, |p.coeff m| ≤ A) :
    coeffL1 p ≤ ((D + 1) ^ n : ℕ) * A := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  calc coeffL1 p ≤ ∑ _m ∈ p.support, A := Finset.sum_le_sum fun m _ => hA m
    _ = p.support.card * A := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((D + 1) ^ n : ℕ) * A := by
        apply mul_le_mul_of_nonneg_right _ hA0
        exact_mod_cast card_support_le p hp

end L1

end Submission.Lib.K4ChartLifting
