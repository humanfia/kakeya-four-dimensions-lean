-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/PolynomialBounds.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PolynomialBounds.lean (namespace renamed).

import Submission.Obl.k4_algebraic_sheet_bound.Anchor

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial Set Metric Finset

abbrev MonomialIndex (n D : ℕ) := Fin n → Fin (D + 1)

noncomputable def monomialExponent {n D : ℕ} (a : MonomialIndex n D) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))

theorem monomialExponent_injective (n D : ℕ) :
    Function.Injective (monomialExponent : MonomialIndex n D → Fin n →₀ ℕ) := by
  intro a b h
  funext i
  apply Fin.ext
  simpa [monomialExponent] using congrArg (fun d : Fin n →₀ ℕ => d i) h

/-- Assemble a polynomial from a finite rectangular array of coefficients. -/
noncomputable def assemblePolynomial (n D : ℕ) :
    (MonomialIndex n D → ℝ) →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  ∑ a, (monomial (monomialExponent a)).comp (LinearMap.proj a)

lemma assemblePolynomial_apply (n D : ℕ) (c : MonomialIndex n D → ℝ) :
    assemblePolynomial n D c = ∑ a, monomial (monomialExponent a) (c a) := by
  simp [assemblePolynomial]

lemma coeff_assemblePolynomial {n D : ℕ} (c : MonomialIndex n D → ℝ)
    (a : MonomialIndex n D) :
    (assemblePolynomial n D c).coeff (monomialExponent a) = c a := by
  classical
  rw [assemblePolynomial_apply, coeff_sum]
  simp [coeff_monomial, (monomialExponent_injective n D).eq_iff]

lemma assemblePolynomial_coefficients {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) :
    assemblePolynomial n D (fun a => P.coeff (monomialExponent a)) = P := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : ∀ i, d i ≤ D
  · let a : MonomialIndex n D := fun i => ⟨d i, Nat.lt_succ_of_le (hd i)⟩
    have heq : monomialExponent a = d := by ext i; simp [monomialExponent, a]
    rw [← heq, coeff_assemblePolynomial]
  · have hPd : P.coeff d = 0 := by
      by_contra hnonzero
      apply hd
      intro i
      exact ((le_degreeOf_of_mem_support i (mem_support_iff.mpr hnonzero)).trans
        (degreeOf_le_totalDegree P i)).trans hP
    rw [assemblePolynomial_apply, coeff_sum, hPd]
    apply sum_eq_zero
    intro a _
    rw [coeff_monomial]
    split_ifs with h
    · exfalso
      apply hd
      intro i
      have hi : d i = a i := by
        simpa [monomialExponent] using (congrArg (fun e : Fin n →₀ ℕ => e i) h).symm
      rw [hi]
      exact Nat.le_of_lt_succ (a i).isLt
    · rfl

noncomputable def polynomialEvaluation (n D : ℕ) :
    (MonomialIndex n D → ℝ) →ₗ[ℝ]
      C(closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2), ℝ) where
  toFun c := ⟨fun x => eval (fun i => x.val i) (assemblePolynomial n D c),
    (assemblePolynomial n D c).continuous_eval.comp (by fun_prop)⟩
  map_add' c d := by ext x; simp
  map_smul' r c := by ext x; simp

/-- Evaluating on the real half-ball detects every coefficient vector. -/
lemma polynomialEvaluation_injective (n D : ℕ) :
    Function.Injective (polynomialEvaluation n D) := by
  classical
  have hker : ∀ c, polynomialEvaluation n D c = 0 → c = 0 := by
    intro c hc
    have hzero (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ (1 : ℝ) / 2) :
        eval (fun i => x i) (assemblePolynomial n D c) = 0 := by
      exact congrArg (fun f : C(closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2), ℝ) =>
        f ⟨x, mem_closedBall_zero_iff.mpr hx⟩) hc
    have hP : assemblePolynomial n D c = 0 := by
      by_contra hnonzero
      have hm : (assemblePolynomial n D c).map (algebraMap ℝ ℂ) ≠ 0 := by
        intro hz
        apply hnonzero
        exact (MvPolynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective)
          (by simpa using hz)
      obtain ⟨x, hx, hval⟩ := Submission.Obl.k4_algebraic_sheet_bound.exists_real_anchor hm
      apply hval
      rw [eval_map]
      calc
        _ = ((eval (fun i => x i) (assemblePolynomial n D c) : ℝ) : ℂ) :=
          (eval₂_comp (algebraMap ℝ ℂ) (fun i => x i) _).symm
        _ = 0 := by rw [hzero x hx]; rfl
    ext a
    simpa [coeff_assemblePolynomial] using
      congrArg (fun P : MvPolynomial (Fin n) ℝ => P.coeff (monomialExponent a)) hP
  intro c d hcd
  exact sub_eq_zero.mp (hker (c - d) (by rw [map_sub, hcd, sub_self]))

/-- On fixed-degree real polynomials, a uniform real half-ball bound controls every
coefficient by one constant depending only on the dimension and degree. -/
theorem exists_polynomial_coefficient_bound (n D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ D →
      ∀ V : ℝ, 0 ≤ V →
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 → |eval (fun i => x i) P| ≤ V) →
      ∀ d, |P.coeff d| ≤ K * V := by
  classical
  obtain ⟨K, hK, hanti⟩ := (polynomialEvaluation n D).injective_iff_antilipschitz.mp
    (polynomialEvaluation_injective n D)
  refine ⟨K, by exact_mod_cast hK, ?_⟩
  intro P hP V hV hbound d
  let c : MonomialIndex n D → ℝ := fun a => P.coeff (monomialExponent a)
  have hPc : assemblePolynomial n D c = P := assemblePolynomial_coefficients P hP
  have hev : ‖polynomialEvaluation n D c‖ ≤ V := by
    apply (ContinuousMap.norm_le _ hV).mpr
    intro x
    change |eval (fun i => x.val i) (assemblePolynomial n D c)| ≤ V
    rw [hPc]
    exact hbound x.val (mem_closedBall_zero_iff.mp x.property)
  have hc := hanti.le_mul_dist c 0
  simp only [dist_zero_right, map_zero] at hc
  have hcV : ‖c‖ ≤ (K : ℝ) * V :=
    hc.trans (mul_le_mul_of_nonneg_left hev K.coe_nonneg)
  by_cases hd : ∀ i, d i ≤ D
  · let a : MonomialIndex n D := fun i => ⟨d i, Nat.lt_succ_of_le (hd i)⟩
    have heq : monomialExponent a = d := by ext i; simp [monomialExponent, a]
    have hh := norm_le_pi_norm c a
    simpa only [c, heq, Real.norm_eq_abs] using hh.trans hcV
  · have hPd : P.coeff d = 0 := by
      by_contra hnonzero
      apply hd
      intro i
      exact ((le_degreeOf_of_mem_support i (mem_support_iff.mpr hnonzero)).trans
        (degreeOf_le_totalDegree P i)).trans hP
    rw [hPd, abs_zero]
    exact mul_nonneg K.coe_nonneg hV

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
