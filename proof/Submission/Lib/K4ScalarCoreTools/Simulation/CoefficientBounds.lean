/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/CoefficientBounds.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 778c2ed,
Submission/Obl/k4_scalar_mesh_projection/CoefficientBounds.lean.
-/

import Mathlib

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Set MvPolynomial

/-- Lagrange interpolation bounds every coefficient of a bounded-degree
univariate polynomial by its sup norm on the unit interval. -/
theorem exists_univariate_coefficient_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℝ), p.natDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ E) →
        ∀ k : ℕ, |p.coeff k| ≤ C * E := by
  classical
  let v : Fin (D + 1) → ℝ := fun k => (k : ℝ) / ((D : ℝ) + 1)
  have hden : 0 < (D : ℝ) + 1 := by positivity
  have hv : Function.Injective v := by
    intro i j hij
    apply Fin.ext
    have hcast : (i : ℝ) = (j : ℝ) := (div_left_inj' hden.ne').mp hij
    exact_mod_cast hcast
  have hvi (i : Fin (D + 1)) : v i ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hden.le
    · apply (div_le_one hden).mpr
      exact_mod_cast Nat.le_of_lt i.isLt
  let W : Fin (D + 1) → ℝ := fun i =>
    ∑ k ∈ (Lagrange.basis Finset.univ v i).support, |(Lagrange.basis Finset.univ v i).coeff k|
  have hW (i : Fin (D + 1)) : 0 ≤ W i :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hWcoeff (i : Fin (D + 1)) (k : ℕ) :
      |(Lagrange.basis Finset.univ v i).coeff k| ≤ W i := by
    by_cases hk : k ∈ (Lagrange.basis Finset.univ v i).support
    · change |(Lagrange.basis Finset.univ v i).coeff k| ≤
        ∑ l ∈ (Lagrange.basis Finset.univ v i).support, |(Lagrange.basis Finset.univ v i).coeff l|
      exact Finset.single_le_sum (f := fun l : ℕ =>
        |(Lagrange.basis Finset.univ v i).coeff l|) (fun _ _ => abs_nonneg _) hk
    · have hz : (Lagrange.basis Finset.univ v i).coeff k = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hk
      simpa only [hz, abs_zero] using hW i
  refine ⟨1 + ∑ i, W i, by
    have : 0 ≤ ∑ i, W i := Finset.sum_nonneg fun i _ => hW i
    linarith, ?_⟩
  intro p hp E hE hb k
  have hdeg : p.degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    apply lt_of_le_of_lt p.degree_le_natDegree
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot, WithBot.coe_lt_coe]
    omega
  have heq := Lagrange.eq_interpolate (s := Finset.univ) hv.injOn hdeg
  have hformula : p.coeff k =
      ∑ i, p.eval (v i) * (Lagrange.basis Finset.univ v i).coeff k := by
    conv_lhs => rw [heq]
    simp [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  rw [hformula]
  calc
    _ ≤ ∑ i, |p.eval (v i) * (Lagrange.basis Finset.univ v i).coeff k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, E * W i := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul (hb _ (hvi i)) (hWcoeff i k) (abs_nonneg _) hE
    _ = (∑ i, W i) * E := by rw [← Finset.mul_sum]; ring
    _ ≤ (1 + ∑ i, W i) * E := by gcongr; linarith

/-- Tensoring the univariate coefficient comparison gives a uniform
bound in every finite dimension, with one fixed factor per variable. -/
theorem exists_multivariate_coefficient_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E →
        (∀ z ∈ Icc (0 : Fin n → ℝ) 1, |eval z P| ≤ E) →
        ∀ e : Fin n →₀ ℕ, |P.coeff e| ≤ C ^ n * E := by
  obtain ⟨C, hC, hcoeff⟩ := exists_univariate_coefficient_constant D
  refine ⟨C, hC, ?_⟩
  intro n
  induction n with
  | zero =>
    intro P hP E hE hb e
    have he : e = 0 := Subsingleton.elim _ _
    have h := hb (0 : Fin 0 → ℝ) ⟨by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩
    simpa only [he, pow_zero, one_mul, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq] using h
  | succ n ih =>
    intro P hP E hE hb e
    let Q := finSuccEquiv ℝ n P
    have hQ : Q.natDegree ≤ D := by
      rw [natDegree_finSuccEquiv]
      exact (degreeOf_le_totalDegree P 0).trans hP
    have hpiece : (Q.coeff (e 0)).totalDegree ≤ D := by
      by_cases hz : Q.coeff (e 0) = 0
      · simp only [hz, totalDegree_zero]; omega
      · have h := totalDegree_coeff_finSuccEquiv_add_le P (e 0) hz
        exact (Nat.le_add_right _ _).trans (h.trans hP)
    have hpieceBound : ∀ z ∈ Icc (0 : Fin n → ℝ) 1,
        |eval z (Q.coeff (e 0))| ≤ C * E := by
      intro z hz
      let p : Polynomial ℝ := Q.map (eval z)
      have hp : p.natDegree ≤ D := Polynomial.natDegree_map_le.trans hQ
      have hpb : ∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ E := by
        intro t ht
        rw [← eval_eq_eval_mv_eval' z t P]
        apply hb
        constructor
        · exact Fin.forall_fin_succ.mpr ⟨ht.1, hz.1⟩
        · exact Fin.forall_fin_succ.mpr ⟨ht.2, hz.2⟩
      simpa only [p, Polynomial.coeff_map] using hcoeff p hp E hE hpb (e 0)
    have h := ih (Q.coeff (e 0)) hpiece (C * E) (mul_nonneg hC.le hE) hpieceBound e.tail
    have hcoef : (Q.coeff (e 0)).coeff e.tail = P.coeff e := by
      rw [finSuccEquiv_coeff_coeff, Finsupp.cons_tail]
    rw [hcoef] at h
    simpa only [pow_succ, mul_assoc] using h

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
