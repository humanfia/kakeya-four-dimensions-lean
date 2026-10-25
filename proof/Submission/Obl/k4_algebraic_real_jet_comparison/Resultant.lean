import Mathlib

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/Resultant.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

/-- Two nonzero complex polynomials become coprime after a suitable translation of one variable. -/
theorem exists_translate_isCoprime (p q : Polynomial ℂ) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ w : ℂ, IsCoprime (p.comp (Polynomial.X + Polynomial.C w)) q := by
  classical
  let E := p.roots.toFinset.biUnion (fun a => q.roots.toFinset.image (fun b => a - b))
  obtain ⟨w, _, hw⟩ := (Set.infinite_univ.sdiff E.finite_toSet).nonempty
  refine ⟨w, (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ _ _).mpr ?_⟩
  intro a
  suffices (p.comp (Polynomial.X + Polynomial.C w)).eval a ≠ 0 ∨ q.eval a ≠ 0 by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using this
  by_cases hqa : q.eval a = 0
  · left
    intro hpa
    have hpa' : p.eval (a + w) = 0 := by simpa using hpa
    apply hw
    apply Finset.mem_biUnion.mpr
    refine ⟨a + w, ?_, ?_⟩
    · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hpa')
    · apply Finset.mem_image.mpr
      exact ⟨a, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr hqa), by ring⟩
  · exact Or.inr hqa

/-- If the entries of a square polynomial matrix have bounded degree, so does its determinant. -/
theorem totalDegree_det_le {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ ℂ)) {D : ℕ}
    (hA : ∀ i j, (A i j).totalDegree ≤ D) :
    A.det.totalDegree ≤ Fintype.card ι * D := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro π hπ
  calc
    _ ≤ (∏ i, A (π i) i).totalDegree := MvPolynomial.totalDegree_smul_le _ _
    _ ≤ ∑ i, (A (π i) i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _i : ι, D := Finset.sum_le_sum fun i _ => hA _ _
    _ = Fintype.card ι * D := by simp

/-- A coefficient degree bound gives a uniform degree bound on a resultant. -/
theorem totalDegree_resultant_le {n : ℕ} (p q : Polynomial (MvPolynomial (Fin n) ℂ))
    (m k D : ℕ) (hp : ∀ j, (p.coeff j).totalDegree ≤ D)
    (hq : ∀ j, (q.coeff j).totalDegree ≤ D) :
    (p.resultant q m k).totalDegree ≤ (m + k) * D := by
  have hA : ∀ i j, ((Polynomial.sylvester p q m k) i j).totalDegree ≤ D := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        split_ifs
        · exact hq _
        · simp
    | right j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        split_ifs
        · exact hp _
        · simp
  simpa only [Polynomial.resultant, Fintype.card_fin] using
    totalDegree_det_le (Polynomial.sylvester p q m k) hA

end Submission.Obl.k4_algebraic_real_jet_comparison
