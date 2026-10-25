import Mathlib
import Submission.Obl.k4_algebraic_sheet_bound.Coeff

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/LinearDegree.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

open MvPolynomial

/-- A fixed linear map from a finite dimensional space has a uniform polynomial degree bound. -/
theorem exists_degree_bound_linear {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {σ : Type*} (L : V →ₗ[ℂ] MvPolynomial σ ℂ) :
    ∃ K : ℕ, ∀ v, (L v).totalDegree ≤ K := by
  classical
  let b := Module.finBasis ℂ V
  refine ⟨Finset.univ.sup (fun i => (L (b i)).totalDegree), ?_⟩
  intro v
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro i hi
  rw [map_smul]
  exact (totalDegree_smul_le _ _).trans (Finset.le_sup (f := fun i => (L (b i)).totalDegree) hi)

/-- The same bound controls both the outer degree and every coefficient's total degree. -/
theorem exists_coefficient_degree_bound_linear {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {n : ℕ}
    (L : V →ₗ[ℂ] Polynomial (MvPolynomial (Fin n) ℂ)) :
    ∃ K : ℕ, ∀ v, (L v).natDegree ≤ K ∧ ∀ j, ((L v).coeff j).totalDegree ≤ K := by
  classical
  let e := MvPolynomial.finSuccEquiv ℂ n
  obtain ⟨K, hK⟩ := exists_degree_bound_linear (e.symm.toLinearMap.comp L)
  refine ⟨K, ?_⟩
  intro v
  have hc (j : ℕ) (hj : (L v).coeff j ≠ 0) :
      ((L v).coeff j).totalDegree + j ≤ K := by
    have h := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le (e.symm (L v)) j
      (by simpa [e] using hj)
    have h' : ((L v).coeff j).totalDegree + j ≤
        (e.symm (L v)).totalDegree := by simpa [e] using h
    exact h'.trans (hK v)
  constructor
  · by_cases hv : L v = 0
    · simp [hv]
    · exact (Nat.le_add_left _ _).trans
        (hc _ (Polynomial.leadingCoeff_ne_zero.mpr hv))
  · intro j
    by_cases hj : (L v).coeff j = 0
    · simp [hj]
    · exact (Nat.le_add_right _ _).trans (hc j hj)

/-- A fixed linear substitution has uniformly bounded complexity on degree-bounded inputs. -/
theorem exists_coefficient_degree_bound (n D m : ℕ)
    (L : MvPolynomial (Fin (n + 1)) ℂ →ₗ[ℂ]
      Polynomial (MvPolynomial (Fin m) ℂ)) :
    ∃ K : ℕ, ∀ P, P.totalDegree ≤ D →
      (L P).natDegree ≤ K ∧ ∀ j, ((L P).coeff j).totalDegree ≤ K := by
  let S := Submission.Obl.k4_algebraic_sheet_bound.PolySpace n D
  obtain ⟨K, hK⟩ := exists_coefficient_degree_bound_linear (L.comp S.subtype)
  refine ⟨K, ?_⟩
  intro P hP
  exact hK ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hP⟩

theorem totalDegree_aeval_le {σ τ : Type*} (g : σ → MvPolynomial τ ℂ)
    {s : ℕ} (hg : ∀ i, (g i).totalDegree ≤ s) (P : MvPolynomial σ ℂ) :
    (aeval g P).totalDegree ≤ s * P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [aeval_eq_eval₂Hom, coe_eval₂Hom, eval₂_monomial]
  calc
    (algebraMap ℂ (MvPolynomial τ ℂ) (P.coeff e) *
      e.prod (fun i k => g i ^ k)).totalDegree
        ≤ 0 + (e.prod (fun i k => g i ^ k)).totalDegree := by
          simpa using totalDegree_mul (C (P.coeff e)) (e.prod (fun i k => g i ^ k))
    _ ≤ ∑ i ∈ e.support, (g i ^ e i).totalDegree := by
      simpa [Finsupp.prod] using totalDegree_finsetProd e.support (fun i => g i ^ e i)
    _ ≤ ∑ i ∈ e.support, e i * s := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))
    _ = s * e.sum (fun _ k => k) := by
      simp only [Finsupp.sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact Nat.mul_comm _ _
    _ ≤ s * P.totalDegree := Nat.mul_le_mul_left s (le_totalDegree he)

end Submission.Obl.k4_algebraic_real_jet_comparison
