/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 5d4285028d58add87cf09665e156b5aba0b683af,
Submission/Obl/k4_scalar_mesh_projection/TensorInterpolation.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Mathlib

namespace Submission.Lib.K4ScalarActualSwitching

open Set MvPolynomial

noncomputable def polynomialOnCoordinate (i : Fin 2) (p : Polynomial ℝ) :
    MvPolynomial (Fin 2) ℝ := p.eval₂ MvPolynomial.C (X i)

theorem eval_polynomialOnCoordinate (i : Fin 2) (p : Polynomial ℝ) (z : Fin 2 → ℝ) :
    eval z (polynomialOnCoordinate i p) = p.eval (z i) := by
  classical
  simp only [polynomialOnCoordinate, Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum,
    Polynomial.sum, map_sum, map_mul, map_pow, eval_C, eval_X]

theorem totalDegree_polynomialOnCoordinate (i : Fin 2) (p : Polynomial ℝ) :
    (polynomialOnCoordinate i p).totalDegree ≤ p.natDegree := by
  classical
  rw [polynomialOnCoordinate, Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply totalDegree_finsetSum_le
  intro n hn
  calc
    (C (p.coeff n) * X i ^ n).totalDegree ≤
        (C (p.coeff n) : MvPolynomial (Fin 2) ℝ).totalDegree + (X i ^ n).totalDegree :=
      totalDegree_mul _ _
    _ = n := by simp
    _ ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)

noncomputable def tensorInterpolant {D : ℕ} (a b : Fin (D + 1) → ℝ)
    (f : ℝ → ℝ → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ i, ∑ j, C (f (a i) (b j)) *
    polynomialOnCoordinate 0 (Lagrange.basis Finset.univ a i) *
    polynomialOnCoordinate 1 (Lagrange.basis Finset.univ b j)

theorem eval_tensorInterpolant {D : ℕ} (a b : Fin (D + 1) → ℝ)
    (f : ℝ → ℝ → ℝ) (x y : ℝ) :
    eval ![x, y] (tensorInterpolant a b f) =
      ∑ i, ∑ j, f (a i) (b j) * (Lagrange.basis Finset.univ a i).eval x *
        (Lagrange.basis Finset.univ b j).eval y := by
  classical
  simp only [tensorInterpolant, map_sum, map_mul, eval_C, eval_polynomialOnCoordinate,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem totalDegree_tensorInterpolant {D : ℕ} (a b : Fin (D + 1) → ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b) (f : ℝ → ℝ → ℝ) :
    (tensorInterpolant a b f).totalDegree ≤ 2 * D := by
  classical
  have hdegree (c : Fin (D + 1) → ℝ) (hc : Function.Injective c) (i : Fin (D + 1)) :
      (Lagrange.basis Finset.univ c i).natDegree = D := by
    simpa using Lagrange.natDegree_basis hc.injOn (Finset.mem_univ i)
  unfold tensorInterpolant
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  have hleft := totalDegree_polynomialOnCoordinate 0 (Lagrange.basis Finset.univ a i)
  have hright := totalDegree_polynomialOnCoordinate 1 (Lagrange.basis Finset.univ b j)
  rw [hdegree a ha i] at hleft
  rw [hdegree b hb j] at hright
  apply (totalDegree_mul _ _).trans
  apply (add_le_add ((totalDegree_mul _ _).trans
    (add_le_add (show (C (f (a i) (b j)) : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 0 by simp)
      hleft)) hright).trans
  omega

theorem polynomial_eval_eq_lagrange {D : ℕ} (a : Fin (D + 1) → ℝ)
    (ha : Function.Injective a) (p : Polynomial ℝ) (hp : p.natDegree ≤ D) (x : ℝ) :
    p.eval x = ∑ i, p.eval (a i) * (Lagrange.basis Finset.univ a i).eval x := by
  classical
  have hdeg : p.degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    apply lt_of_le_of_lt p.degree_le_natDegree
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot, WithBot.coe_lt_coe]
    omega
  have heq := Lagrange.eq_interpolate (s := Finset.univ) ha.injOn hdeg
  conv_lhs => rw [heq]
  simp [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]

theorem lagrange_approximation_error {D : ℕ} (a : Fin (D + 1) → ℝ)
    (ha : Function.Injective a) (p : Polynomial ℝ) (hp : p.natDegree ≤ D)
    (f : ℝ → ℝ) (x E : ℝ) (hE : 0 ≤ E)
    (hx : |f x - p.eval x| ≤ E) (hnodes : ∀ i, |f (a i) - p.eval (a i)| ≤ E) :
    |f x - ∑ i, f (a i) * (Lagrange.basis Finset.univ a i).eval x| ≤
      E * (1 + ∑ i, |(Lagrange.basis Finset.univ a i).eval x|) := by
  classical
  have hsum : |p.eval x - ∑ i, f (a i) * (Lagrange.basis Finset.univ a i).eval x| ≤
      E * ∑ i, |(Lagrange.basis Finset.univ a i).eval x| := by
    rw [polynomial_eval_eq_lagrange a ha p hp x, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i, E * |(Lagrange.basis Finset.univ a i).eval x| :=
        Finset.sum_le_sum fun i _ => by
          rw [← sub_mul, abs_mul]
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          simpa only [abs_sub_comm] using hnodes i
      _ = E * ∑ i, |(Lagrange.basis Finset.univ a i).eval x| := (Finset.mul_sum ..).symm
  have h := (abs_sub_le (f x) (p.eval x)
    (∑ i, f (a i) * (Lagrange.basis Finset.univ a i).eval x)).trans (add_le_add hx hsum)
  convert h using 1
  ring

/-- The pure anchor values determine a single polynomial. Each target
needs only its horizontal fiber and the anchor vertical fibers to fit
degree-D polynomials at the required grid vertices. -/
theorem tensor_interpolation_error {D : ℕ} (a b : Fin (D + 1) → ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b) (f : ℝ → ℝ → ℝ)
    (x y E : ℝ) (hE : 0 ≤ E)
    (hrow : ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ |f x y - p.eval x| ≤ E ∧
      ∀ i, |f (a i) y - p.eval (a i)| ≤ E)
    (hcols : ∀ i, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ |f (a i) y - p.eval y| ≤ E ∧
      ∀ j, |f (a i) (b j) - p.eval (b j)| ≤ E) :
    |f x y - eval ![x, y] (tensorInterpolant a b f)| ≤
      E * (1 + 2 * (∑ i, |(Lagrange.basis Finset.univ a i).eval x|) +
        (∑ i, |(Lagrange.basis Finset.univ a i).eval x|) *
          (∑ j, |(Lagrange.basis Finset.univ b j).eval y|)) := by
  classical
  let A := ∑ i, f (a i) y * (Lagrange.basis Finset.univ a i).eval x
  let V := ∑ j, |(Lagrange.basis Finset.univ b j).eval y|
  obtain ⟨p, hp, htarget, hnodes⟩ := hrow
  have hhor := lagrange_approximation_error a ha p hp (fun x => f x y) x E hE htarget hnodes
  have hver (i : Fin (D + 1)) :
      |f (a i) y - ∑ j, f (a i) (b j) * (Lagrange.basis Finset.univ b j).eval y| ≤
        E * (1 + V) := by
    obtain ⟨p, hp, htarget, hnodes⟩ := hcols i
    exact lagrange_approximation_error b hb p hp (f (a i)) y E hE htarget hnodes
  have hdiff : |A - eval ![x, y] (tensorInterpolant a b f)| ≤
      E * (1 + V) * ∑ i, |(Lagrange.basis Finset.univ a i).eval x| := by
    rw [eval_tensorInterpolant]
    have hid : A - ∑ i, ∑ j, f (a i) (b j) * (Lagrange.basis Finset.univ a i).eval x *
        (Lagrange.basis Finset.univ b j).eval y =
        ∑ i, (f (a i) y - ∑ j, f (a i) (b j) * (Lagrange.basis Finset.univ b j).eval y) *
          (Lagrange.basis Finset.univ a i).eval x := by
      dsimp only [A]
      simp only [Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hid]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i, (E * (1 + V)) * |(Lagrange.basis Finset.univ a i).eval x| :=
        Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hver i) (abs_nonneg _)
      _ = _ := (Finset.mul_sum ..).symm
  have h := (abs_sub_le (f x y) A (eval ![x, y] (tensorInterpolant a b f))).trans
    (add_le_add hhor hdiff)
  convert h using 1
  dsimp only [V]
  ring

theorem lagrange_basis_eval_bound {D : ℕ} (a : Fin (D + 1) → ℝ)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (ha : ∀ i, |a i| ≤ R) (hsep : ∀ i j, i ≠ j → δ ≤ |a i - a j|)
    (x : ℝ) (hx : |x| ≤ R) (i : Fin (D + 1)) :
    |(Lagrange.basis Finset.univ a i).eval x| ≤ (2 * R / δ) ^ D := by
  classical
  rw [Lagrange.basis, Polynomial.eval_prod, Finset.abs_prod]
  calc
    _ ≤ ∏ j ∈ (Finset.univ : Finset (Fin (D + 1))).erase i, (2 * R / δ) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact abs_nonneg _
      · intro j hj
        have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
        have hden := hsep i j hij
        have hdenp : 0 < |a i - a j| := hδ.trans_le hden
        have hnum : |x - a j| ≤ 2 * R := by
          have h := abs_sub_le x 0 (a j)
          simp only [sub_zero, zero_sub, abs_neg] at h
          linarith [ha j]
        simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X, abs_mul, abs_inv]
        rw [mul_comm, ← div_eq_mul_inv]
        apply (div_le_iff₀ hdenp).mpr
        calc
          |x - a j| ≤ 2 * R := hnum
          _ = (2 * R / δ) * δ := by field_simp [hδ.ne']
          _ ≤ (2 * R / δ) * |a i - a j| :=
            mul_le_mul_of_nonneg_left hden (div_nonneg (by positivity) hδ.le)
    _ = _ := by simp [div_pow]

theorem lagrange_weight_sum_bound {D : ℕ} (a : Fin (D + 1) → ℝ)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (ha : ∀ i, |a i| ≤ R) (hsep : ∀ i j, i ≠ j → δ ≤ |a i - a j|)
    (x : ℝ) (hx : |x| ≤ R) :
    (∑ i, |(Lagrange.basis Finset.univ a i).eval x|) ≤
      ((D : ℝ) + 1) * (2 * R / δ) ^ D := by
  classical
  calc
    _ ≤ ∑ i : Fin (D + 1), (2 * R / δ) ^ D :=
      Finset.sum_le_sum fun i _ => lagrange_basis_eval_bound a R δ hR hδ ha hsep x hx i
    _ = _ := by simp [Nat.cast_add, Nat.cast_one]

/-- Uniform conditioning of the tensor interpolant on a bounded box.
The inverse-gap loss has a fixed exponent depending only on the degree. -/
theorem tensor_interpolant_eval_bound {D : ℕ} (a b : Fin (D + 1) → ℝ)
    (f : ℝ → ℝ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hvals : ∀ i j, |f (a i) (b j)| ≤ H) (x y : ℝ) :
    |eval ![x, y] (tensorInterpolant a b f)| ≤
      H * (∑ i, |(Lagrange.basis Finset.univ a i).eval x|) *
        (∑ j, |(Lagrange.basis Finset.univ b j).eval y|) := by
  classical
  rw [eval_tensorInterpolant]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i, ∑ j, H * |(Lagrange.basis Finset.univ a i).eval x| *
        |(Lagrange.basis Finset.univ b j).eval y| := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hvals i j) (abs_nonneg _)) (abs_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

end Submission.Lib.K4ScalarActualSwitching
