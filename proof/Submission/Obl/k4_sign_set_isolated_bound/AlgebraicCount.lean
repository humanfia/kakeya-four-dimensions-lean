import Mathlib

noncomputable section

namespace Submission.Obl.k4_sign_set_isolated_bound

open MvPolynomial Set
open scoped BigOperators

/-- Evaluating polynomials on distinct finitely many points gives every function on those points. -/
theorem eval_finite_surjective {ι σ : Type*} [Fintype ι]
    (v : ι → σ → ℝ) (hv : Function.Injective v) :
    Function.Surjective (MvPolynomial.aeval (fun j a => v a j) :
      MvPolynomial σ ℝ →ₐ[ℝ] (ι → ℝ)) := by
  classical
  let E : MvPolynomial σ ℝ →ₐ[ℝ] (ι → ℝ) := MvPolynomial.aeval (fun j a => v a j)
  have sep (a b : ι) (hab : a ≠ b) : ∃ j, v a j ≠ v b j := by
    by_contra! h
    exact hab (hv (funext h))
  let L (a b : ι) : MvPolynomial σ ℝ :=
    if h : a = b then 1 else
      C ((v a (sep a b h).choose - v b (sep a b h).choose)⁻¹) *
        (X (sep a b h).choose - C (v b (sep a b h).choose))
  have La (a b : ι) : E (L a b) a = 1 := by
    dsimp [L]
    split_ifs with h
    · simp
    · simp only [E, map_mul, map_sub, aeval_C, aeval_X, Pi.mul_apply, Pi.sub_apply,
        Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (sep a b h).choose_spec)
  have Lb (a b : ι) (h : a ≠ b) : E (L a b) b = 0 := by
    simp [L, h, E]
  let P (a : ι) : MvPolynomial σ ℝ := ∏ b, L a b
  have EP (a b : ι) : E (P a) b = if a = b then 1 else 0 := by
    by_cases h : a = b
    · subst b
      simp [P, La]
    · simp only [h, ↓reduceIte, P, map_prod, Finset.prod_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ b) (Lb a b h)
  intro f
  refine ⟨∑ a, C (f a) * P a, ?_⟩
  change E (∑ a, C (f a) * P a) = f
  ext b
  simp [EP, E, Finset.sum_ite_eq']

/-- Relations with a pure leading power reduce every polynomial to bounded exponents. -/
theorem eval_mem_bounded_degree {σ A : Type*} [Fintype σ] [CommRing A] [Algebra ℝ A]
    (k : ℕ) (q : σ → MvPolynomial σ ℝ) (hq : ∀ i, (q i).totalDegree < k)
    (E : MvPolynomial σ ℝ →ₐ[ℝ] A) (hE : ∀ i, E (X i ^ k) = E (q i))
    (p : MvPolynomial σ ℝ) :
    E p ∈ (MvPolynomial.restrictDegree σ ℝ k).map E.toLinearMap := by
  classical
  let W := (MvPolynomial.restrictDegree σ ℝ k).map E.toLinearMap
  change E p ∈ W
  induction hn : p.totalDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    have mon (a : σ →₀ ℕ) (r : ℝ) (ha : a ∈ p.support) : E (monomial a r) ∈ W := by
      by_cases hb : ∀ i, a i ≤ k
      · apply Submodule.mem_map.mpr
        refine ⟨monomial a r, ?_, rfl⟩
        rw [MvPolynomial.mem_restrictDegree]
        intro b hba
        by_cases hr : r = 0
        · simp [hr] at hba
        · have : b = a := by simpa [MvPolynomial.support_monomial, hr] using hba
          subst b
          exact hb
      · obtain ⟨i, hi⟩ := not_forall.mp hb
        have hki : k ≤ a i := le_of_lt (lt_of_not_ge hi)
        let b := a - Finsupp.single i k
        have hab : b + Finsupp.single i k = a :=
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hki)
        have hs : b.sum (fun _ e => e) + k = a.sum (fun _ e => e) := by
          rw [← hab, Finsupp.sum_add_index'] <;> simp
        have hdeg : (monomial b r * q i).totalDegree < n := by
          have h₁ := MvPolynomial.totalDegree_mul (monomial b r) (q i)
          have h₂ : (monomial b r).totalDegree ≤ b.sum (fun _ e => e) :=
            MvPolynomial.totalDegree_monomial_le b r
          have h₃ := MvPolynomial.le_totalDegree ha
          have h₄ := hq i
          omega
        have heq : E (monomial a r) = E (monomial b r * q i) := by
          rw [map_mul, ← hE i, ← map_mul]
          congr 1
          rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, mul_one, hab]
        rw [heq]
        exact ih _ hdeg _ rfl
    have hp : E p = ∑ a ∈ p.support, E (monomial a (p.coeff a)) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
    rw [hp]
    exact Submodule.sum_mem W (fun a ha => mon a _ ha)

/-- A uniform bound for distinct solutions of polynomial equations with pure leading powers. -/
theorem card_le_of_pure_power_relations {ι σ : Type*} [Fintype ι] [Fintype σ]
    (k : ℕ) (q : σ → MvPolynomial σ ℝ) (hq : ∀ i, (q i).totalDegree < k)
    (v : ι → σ → ℝ) (hv : Function.Injective v)
    (hroot : ∀ a i, v a i ^ k = MvPolynomial.eval (v a) (q i)) :
    Fintype.card ι ≤ Module.finrank ℝ (MvPolynomial.restrictDegree σ ℝ k) := by
  let E : MvPolynomial σ ℝ →ₐ[ℝ] (ι → ℝ) := MvPolynomial.aeval (fun j a => v a j)
  have hE : ∀ i, E (X i ^ k) = E (q i) := by
    intro i
    ext a
    have ev (p : MvPolynomial σ ℝ) : E p a = MvPolynomial.eval (v a) p := by
      induction p using MvPolynomial.induction_on with
      | C r => simp [E]
      | add p q hp hq => simp [hp, hq]
      | mul_X p j hp => simp [E, hp]
    simpa [ev] using hroot a i
  have htop : (MvPolynomial.restrictDegree σ ℝ k).map E.toLinearMap = ⊤ := by
    apply top_unique
    intro f _
    obtain ⟨p, rfl⟩ := eval_finite_surjective v hv f
    exact eval_mem_bounded_degree k q hq E hE p
  have hdim := Submodule.finrank_map_le E.toLinearMap
    (MvPolynomial.restrictDegree σ ℝ k)
  rw [htop, finrank_top, Module.finrank_pi] at hdim
  simpa using hdim

end Submission.Obl.k4_sign_set_isolated_bound
