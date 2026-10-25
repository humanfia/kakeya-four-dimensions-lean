import Mathlib
import Submission.Obl.k4_algebraic_sheet_bound.LastVar
import Submission.Obl.k4_algebraic_sheet_bound.Anchor
import Submission.Obl.k4_algebraic_real_jet_comparison.LinearDegree
import Submission.Obl.k4_algebraic_real_jet_comparison.Resultant
/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/AlgebraicClosure.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison
open MvPolynomial
noncomputable def lastEquiv (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin n) ℂ) :=
  (MvPolynomial.renameEquiv ℂ (finRotate (n + 1))).trans (MvPolynomial.finSuccEquiv ℂ n)
noncomputable def extendedPoly {n : ℕ} :
    Polynomial (MvPolynomial (Fin n) ℂ) →ₐ[ℂ] Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
  Polynomial.mapAlgHom (MvPolynomial.rename Fin.castSucc)
noncomputable def shiftedPoly {n : ℕ} :
    Polynomial (MvPolynomial (Fin n) ℂ) →ₐ[ℂ] Polynomial (MvPolynomial (Fin (n + 1)) ℂ) :=
  ((Polynomial.aeval (Polynomial.X + Polynomial.C (MvPolynomial.X (Fin.last n)))).restrictScalars ℂ).comp extendedPoly
lemma extendedPoly_apply {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) :
    extendedPoly p = p.map (MvPolynomial.rename Fin.castSucc).toRingHom := rfl
lemma shiftedPoly_apply {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) :
    shiftedPoly p = (extendedPoly p).comp (Polynomial.X + Polynomial.C (MvPolynomial.X (Fin.last n))) := rfl
lemma natDegree_extendedPoly {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) :
    (extendedPoly p).natDegree = p.natDegree := by
  apply Polynomial.natDegree_map_eq_of_injective
  exact MvPolynomial.rename_injective _ (Fin.castSucc_injective n)
lemma natDegree_shiftedPoly {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) :
    (shiftedPoly p).natDegree = p.natDegree := by
  rw [shiftedPoly_apply, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C,
    mul_one, natDegree_extendedPoly]
lemma map_extendedPoly {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (z : Fin n → ℂ) (w : ℂ) :
    (extendedPoly p).map (MvPolynomial.eval (Fin.snoc z w)) = p.map (MvPolynomial.eval z) := by
  rw [extendedPoly_apply, Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    simp
lemma map_shiftedPoly {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (z : Fin n → ℂ) (w : ℂ) :
    (shiftedPoly p).map (MvPolynomial.eval (Fin.snoc z w)) =
      (p.map (MvPolynomial.eval z)).comp (Polynomial.X + Polynomial.C w) := by
  rw [shiftedPoly_apply, Polynomial.map_comp, map_extendedPoly]
  simp

/-- The translated resultant is a nonzero polynomial in the base and difference variables. -/
theorem shifted_resultant_ne_zero {n : ℕ}
    (p q : Polynomial (MvPolynomial (Fin n) ℂ)) (hp : p ≠ 0) (hq : q ≠ 0) :
    (shiftedPoly p).resultant (extendedPoly q) p.natDegree q.natDegree ≠ 0 := by
  classical
  obtain ⟨x, hx, hx0⟩ := Submission.Obl.k4_algebraic_sheet_bound.exists_real_anchor
    (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp)
      (Polynomial.leadingCoeff_ne_zero.mpr hq))
  let z : Fin n → ℂ := fun i => (x i : ℂ)
  have hz : eval z p.leadingCoeff ≠ 0 ∧ eval z q.leadingCoeff ≠ 0 := by
    simpa only [map_mul, ne_eq, mul_eq_zero, not_or] using hx0
  let pz := p.map (eval z)
  let qz := q.map (eval z)
  have hpz : pz ≠ 0 := by
    intro h
    apply hz.1
    have h' := congrArg (fun r : Polynomial ℂ => r.coeff p.natDegree) h
    simpa only [pz, Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coeff_natDegree] using h'
  have hqz : qz ≠ 0 := by
    intro h
    apply hz.2
    have h' := congrArg (fun r : Polynomial ℂ => r.coeff q.natDegree) h
    simpa only [qz, Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coeff_natDegree] using h'
  have hpdeg : pz.natDegree = p.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hz.1
  have hqdeg : qz.natDegree = q.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hz.2
  obtain ⟨w, hw⟩ := exists_translate_isCoprime pz qz hpz hqz
  have hres := Polynomial.resultant_ne_zero _ _ hw
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one, hpdeg, hqdeg] at hres
  intro hzero
  apply hres
  calc
    (pz.comp (Polynomial.X + Polynomial.C w)).resultant qz p.natDegree q.natDegree =
        eval (Fin.snoc z w)
          ((shiftedPoly p).resultant (extendedPoly q) p.natDegree q.natDegree) := by
      rw [← Polynomial.resultant_map_map, map_shiftedPoly, map_extendedPoly]
    _ = 0 := by rw [hzero, map_zero]


/-- A common root forces every specialization of the resultant to vanish, even when degrees drop. -/
theorem eval_resultant_eq_zero {R S : Type*} [CommRing R] [CommRing S]
    (p q : Polynomial R) (m k : ℕ) (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ k)
    (hpos : m ≠ 0 ∨ k ≠ 0) (φ : R →+* S) (a : S)
    (hpa : (p.map φ).eval a = 0) (hqa : (q.map φ).eval a = 0) :
    φ (p.resultant q m k) = 0 := by
  obtain ⟨u, v, hu, hv, huv⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant p q hp hq hpos
  have he := congrArg (Polynomial.eval₂ φ a) huv
  simpa only [Polynomial.eval₂_eq_eval_map, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    hpa, hqa, zero_mul, zero_add] using he.symm

/-- Differences of two bounded-degree algebraic sheets have a bounded-degree relation.
No coefficient lower bound or simplicity hypothesis is used. -/
theorem exists_difference_degree_bound (n D : ℕ) :
    ∃ E : ℕ, ∀ (P Q : MvPolynomial (Fin (n + 1)) ℂ),
      P ≠ 0 → Q ≠ 0 → P.totalDegree ≤ D → Q.totalDegree ≤ D →
      ∃ S : MvPolynomial (Fin (n + 1)) ℂ, S ≠ 0 ∧ S.totalDegree ≤ E ∧
        ∀ (z : Fin n → ℂ) (a b : ℂ), eval (Fin.snoc z a) P = 0 →
          eval (Fin.snoc z b) Q = 0 → eval (Fin.snoc z (a - b)) S = 0 := by
  classical
  let LP := shiftedPoly.toLinearMap.comp (lastEquiv n).toLinearMap
  let LQ := extendedPoly.toLinearMap.comp (lastEquiv n).toLinearMap
  obtain ⟨K₁, hK₁⟩ := exists_coefficient_degree_bound n D (n + 1) LP
  obtain ⟨K₂, hK₂⟩ := exists_coefficient_degree_bound n D (n + 1) LQ
  let K := max K₁ K₂
  refine ⟨(2 * K + 1) * K, ?_⟩
  intro P Q hP hQ hPD hQD
  let p := Submission.Obl.k4_algebraic_sheet_bound.lastVar P
  let q := Submission.Obl.k4_algebraic_sheet_bound.lastVar Q
  have hp : p ≠ 0 := Submission.Obl.k4_algebraic_sheet_bound.lastVar_ne_zero hP
  have hq : q ≠ 0 := Submission.Obl.k4_algebraic_sheet_bound.lastVar_ne_zero hQ
  have hshift : (shiftedPoly p).natDegree ≤ K ∧
      ∀ j, ((shiftedPoly p).coeff j).totalDegree ≤ K := by
    obtain ⟨h₁, h₂⟩ := hK₁ P hPD
    exact ⟨h₁.trans (le_max_left _ _), fun j => (h₂ j).trans (le_max_left _ _)⟩
  have hext : (extendedPoly q).natDegree ≤ K ∧
      ∀ j, ((extendedPoly q).coeff j).totalDegree ≤ K := by
    obtain ⟨h₁, h₂⟩ := hK₂ Q hQD
    exact ⟨h₁.trans (le_max_right _ _), fun j => (h₂ j).trans (le_max_right _ _)⟩
  have hbound : K ≤ (2 * K + 1) * K := by nlinarith
  by_cases hp0 : p.natDegree = 0
  · have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hp0
    refine ⟨(extendedPoly p).coeff 0, ?_, ?_, ?_⟩
    · intro hzero
      apply hp
      rw [hpC]
      suffices p.coeff 0 = 0 by simp only [this, Polynomial.C_0]
      apply MvPolynomial.rename_injective _ (Fin.castSucc_injective n)
      simpa [extendedPoly_apply] using hzero
    · exact ((hK₂ P hPD).2 0).trans ((le_max_right _ _).trans hbound)
    · intro z a b hpa hqb
      rw [Submission.Obl.k4_algebraic_sheet_bound.eval_snoc_eq_lastVar] at hpa
      change (p.map (eval z)).eval a = 0 at hpa
      rw [hpC] at hpa ⊢
      simpa [extendedPoly_apply, MvPolynomial.eval_rename] using hpa
  · refine ⟨(shiftedPoly p).resultant (extendedPoly q) p.natDegree q.natDegree,
      shifted_resultant_ne_zero p q hp hq, ?_, ?_⟩
    · have hpd : p.natDegree ≤ K := by simpa only [natDegree_shiftedPoly] using hshift.1
      have hqd : q.natDegree ≤ K := by simpa only [natDegree_extendedPoly] using hext.1
      exact (totalDegree_resultant_le _ _ _ _ K hshift.2 hext.2).trans
        (by nlinarith)
    · intro z a b hpa hqb
      rw [Submission.Obl.k4_algebraic_sheet_bound.eval_snoc_eq_lastVar] at hpa hqb
      apply eval_resultant_eq_zero _ _ _ _ (by rw [natDegree_shiftedPoly])
        (by rw [natDegree_extendedPoly]) (Or.inl hp0) (eval (Fin.snoc z (a - b))) b
      · rw [map_shiftedPoly]
        simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_C, add_sub_cancel] using hpa
      · rw [map_extendedPoly]
        exact hqb

end Submission.Obl.k4_algebraic_real_jet_comparison
