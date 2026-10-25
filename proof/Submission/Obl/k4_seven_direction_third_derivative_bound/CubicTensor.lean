/-
Adapted from: here:root
Original proofs by session x0001, root branch x0001-cubiclib, commit f6ada26.
Source: Submission/Lib/K4CubicTests/CubicTensor.lean.
This helper has not entered lib; only the cubic two-copy argument is used here.
-/
import Mathlib

/-!
The injectivity assertion in paper Lemma 6.6, part 2. In fact three basis
directions and a fourth direction with suitable nonzero coordinates suffice.
-/

namespace Submission.Obl.k4_seven_direction_third_derivative_bound

section Cubic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An explicit inverse formula for the one cubic coefficient not directly
seen by the tests at the basis vectors. It also gives polynomial conditioning. -/
theorem cubic_mixed_coefficient_identity
    (b : Module.Basis (Fin 3) ℝ E)
    (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (h01 : ∀ x y z, T x y z = T y x z)
    (h12 : ∀ x y z, T x y z = T x z y) (v : E) :
    2 * b.repr v 1 * b.repr v 2 * T (b 0) (b 1) (b 2) =
      T v v (b 0) - (b.repr v 0) ^ 2 * T (b 0) (b 0) (b 0) -
      2 * b.repr v 0 * b.repr v 1 * T (b 0) (b 0) (b 1) -
      2 * b.repr v 0 * b.repr v 2 * T (b 0) (b 0) (b 2) -
      (b.repr v 1) ^ 2 * T (b 1) (b 1) (b 0) -
      (b.repr v 2) ^ 2 * T (b 2) (b 2) (b 0) := by
  have hexp : v = b.repr v 0 • b 0 + (b.repr v 1 • b 1 + b.repr v 2 • b 2) := by
    simpa only [Fin.sum_univ_three, add_assoc] using (b.sum_repr v).symm
  have h010 : T (b 0) (b 1) (b 0) = T (b 0) (b 0) (b 1) := h12 _ _ _
  have h100 : T (b 1) (b 0) (b 0) = T (b 0) (b 0) (b 1) := (h01 _ _ _).trans h010
  have h020 : T (b 0) (b 2) (b 0) = T (b 0) (b 0) (b 2) := h12 _ _ _
  have h200 : T (b 2) (b 0) (b 0) = T (b 0) (b 0) (b 2) := (h01 _ _ _).trans h020
  have h120 : T (b 1) (b 2) (b 0) = T (b 0) (b 1) (b 2) :=
    (h12 _ _ _).trans (h01 _ _ _)
  have h210 : T (b 2) (b 1) (b 0) = T (b 0) (b 1) (b 2) := (h01 _ _ _).trans h120
  have h : T v v (b 0) =
      (b.repr v 0) ^ 2 * T (b 0) (b 0) (b 0) +
      2 * b.repr v 0 * b.repr v 1 * T (b 0) (b 0) (b 1) +
      2 * b.repr v 0 * b.repr v 2 * T (b 0) (b 0) (b 2) +
      (b.repr v 1) ^ 2 * T (b 1) (b 1) (b 0) +
      2 * b.repr v 1 * b.repr v 2 * T (b 0) (b 1) (b 2) +
      (b.repr v 2) ^ 2 * T (b 2) (b 2) (b 0) := by
    calc
      T v v (b 0) = T
          (b.repr v 0 • b 0 + (b.repr v 1 • b 1 + b.repr v 2 • b 2))
          (b.repr v 0 • b 0 + (b.repr v 1 • b 1 + b.repr v 2 • b 2)) (b 0) := by
        simp only [← hexp]
      _ = _ := by
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, h010, h100, h020, h200, h120, h210]
        ring
  linarith

/-- Explicit polynomial conditioning for the cubic two-copy tests, measured in
a chosen basis. Upper coordinate bounds and reciprocal lower bounds on two
coordinates give the loss `4 A^4`. -/
theorem cubic_coefficients_le_of_two_copy_tests
    (b : Module.Basis (Fin 3) ℝ E)
    (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (h01 : ∀ x y z, T x y z = T y x z)
    (h12 : ∀ x y z, T x y z = T x z y)
    (v : E) (A ε : ℝ) (hA : 1 ≤ A) (hε : 0 ≤ ε)
    (hα : ∀ i : Fin 3, |b.repr v i| ≤ A)
    (hlow1 : 1 ≤ A * |b.repr v 1|) (hlow2 : 1 ≤ A * |b.repr v 2|)
    (hB : ∀ i j : Fin 3, |T (b i) (b i) (b j)| ≤ ε)
    (hv : |T v v (b 0)| ≤ ε) :
    ∀ i j k : Fin 3, |T (b i) (b j) (b k)| ≤ 4 * A ^ 4 * ε := by
  have hA0 : 0 ≤ A := by linarith
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hA4 : 1 ≤ A ^ 4 := by nlinarith [sq_nonneg (A ^ 2 - 1)]
  let α : Fin 3 → ℝ := fun i => b.repr v i
  let c : ℝ := T (b 0) (b 1) (b 2)
  let t0 : ℝ := α 0 ^ 2 * T (b 0) (b 0) (b 0)
  let t1 : ℝ := 2 * α 0 * α 1 * T (b 0) (b 0) (b 1)
  let t2 : ℝ := 2 * α 0 * α 2 * T (b 0) (b 0) (b 2)
  let t3 : ℝ := α 1 ^ 2 * T (b 1) (b 1) (b 0)
  let t4 : ℝ := α 2 ^ 2 * T (b 2) (b 2) (b 0)
  have hrec : 2 * α 1 * α 2 * c = T v v (b 0) - t0 - t1 - t2 - t3 - t4 :=
    cubic_mixed_coefficient_identity b T h01 h12 v
  have ht0 : |t0| ≤ A ^ 2 * ε := by
    dsimp [t0]
    simp only [abs_mul, abs_pow]
    gcongr <;> first | exact hα 0 | exact hB 0 0
  have ht1 : |t1| ≤ 2 * A ^ 2 * ε := by
    dsimp [t1]
    simp only [abs_mul, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    calc
      2 * |α 0| * |α 1| * |T (b 0) (b 0) (b 1)| ≤ 2 * A * A * ε := by
        gcongr <;> first | exact hα 0 | exact hα 1 | exact hB 0 1
      _ = _ := by ring
  have ht2 : |t2| ≤ 2 * A ^ 2 * ε := by
    dsimp [t2]
    simp only [abs_mul, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    calc
      2 * |α 0| * |α 2| * |T (b 0) (b 0) (b 2)| ≤ 2 * A * A * ε := by
        gcongr <;> first | exact hα 0 | exact hα 2 | exact hB 0 2
      _ = _ := by ring
  have ht3 : |t3| ≤ A ^ 2 * ε := by
    dsimp [t3]
    simp only [abs_mul, abs_pow]
    gcongr <;> first | exact hα 1 | exact hB 1 0
  have ht4 : |t4| ≤ A ^ 2 * ε := by
    dsimp [t4]
    simp only [abs_mul, abs_pow]
    gcongr <;> first | exact hα 2 | exact hB 2 0
  have habs : |T v v (b 0) - t0 - t1 - t2 - t3 - t4| ≤
      |T v v (b 0)| + |t0| + |t1| + |t2| + |t3| + |t4| := by
    simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using
      (Finset.abs_sum_le_sum_abs
        (fun i : Fin 6 => (![T v v (b 0), -t0, -t1, -t2, -t3, -t4] : Fin 6 → ℝ) i)
        Finset.univ)
  have hbound : |2 * α 1 * α 2 * c| ≤ 8 * A ^ 2 * ε := by
    rw [hrec]
    have hscale := mul_le_mul_of_nonneg_right hA2 hε
    linarith
  have hprod : 1 ≤ A ^ 2 * |α 1| * |α 2| := by
    have h := mul_le_mul hlow1 hlow2 zero_le_one (by positivity : 0 ≤ A * |b.repr v 1|)
    dsimp [α]
    nlinarith
  have hc : |c| ≤ 4 * A ^ 4 * ε := by
    have hmul := mul_le_mul_of_nonneg_right hprod (by positivity : 0 ≤ 2 * |c|)
    have htwo : 2 * |c| ≤ 8 * A ^ 4 * ε := by
      calc
        2 * |c| ≤ (A ^ 2 * |α 1| * |α 2|) * (2 * |c|) := by simpa using hmul
        _ = A ^ 2 * |2 * α 1 * α 2 * c| := by simp only [abs_mul, abs_of_pos (by norm_num : 0 < (2 : ℝ))]; ring
        _ ≤ A ^ 2 * (8 * A ^ 2 * ε) := mul_le_mul_of_nonneg_left hbound (sq_nonneg A)
        _ = _ := by ring
    linarith
  have hε' : ε ≤ 4 * A ^ 4 * ε := by
    nlinarith [mul_le_mul_of_nonneg_right hA4 hε]
  have hrep (i j k : Fin 3) (h : i = j ∨ i = k ∨ j = k) :
      |T (b i) (b j) (b k)| ≤ ε := by
    rcases h with h | h | h
    · subst j
      exact hB i k
    · subst k
      rw [h12]
      exact hB i j
    · subst k
      rw [h01, h12]
      exact hB j i
  have h021 : T (b 0) (b 2) (b 1) = c := h12 _ _ _
  have h102 : T (b 1) (b 0) (b 2) = c := h01 _ _ _
  have h120 : T (b 1) (b 2) (b 0) = c := (h12 _ _ _).trans h102
  have h201 : T (b 2) (b 0) (b 1) = c := (h01 _ _ _).trans h021
  have h210 : T (b 2) (b 1) (b 0) = c := (h12 _ _ _).trans h201
  intro i j k
  by_cases h : i = j ∨ i = k ∨ j = k
  · exact (hrep i j k h).trans hε'
  · fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at h
    all_goals first
      | exact hc
      | exact (congrArg abs h021).trans_le hc
      | exact (congrArg abs h102).trans_le hc
      | exact (congrArg abs h120).trans_le hc
      | exact (congrArg abs h201).trans_le hc
      | exact (congrArg abs h210).trans_le hc

end Cubic

end Submission.Obl.k4_seven_direction_third_derivative_bound
