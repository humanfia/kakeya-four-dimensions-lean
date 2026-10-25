import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.LinearDegree

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/AffineRelations.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

open MvPolynomial

/-- Affine change of the base coordinates and scaling of the sheet coordinate. -/
noncomputable def affineRelation {n : ℕ} (a : Fin n → ℂ) (r s : ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (n + 1)) ℂ :=
  aeval (Fin.snoc (fun i : Fin n => C (a i) + C r * X i.castSucc)
    (C s * X (Fin.last n)))

lemma eval_affineRelation {n : ℕ} (a z : Fin n → ℂ) (r s w : ℂ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    eval (Fin.snoc z w) (affineRelation a r s P) =
      eval (Fin.snoc (fun i => a i + r * z i) (s * w)) P := by
  have he : (eval (Fin.snoc z w)).comp (affineRelation a r s).toRingHom =
      eval (Fin.snoc (fun i => a i + r * z i) (s * w)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineRelation]
    · intro i
      induction i using Fin.lastCases with
      | last => simp [affineRelation]
      | cast i => simp [affineRelation]
  exact congrArg (fun h : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ => h P) he

lemma affineRelation_injective {n : ℕ} (a : Fin n → ℂ) {r s : ℂ}
    (hr : r ≠ 0) (hs : s ≠ 0) : Function.Injective (affineRelation a r s) := by
  have he : (affineRelation (fun i => -(r⁻¹ * a i)) r⁻¹ s⁻¹).comp
      (affineRelation a r s) = AlgHom.id ℂ (MvPolynomial (Fin (n + 1)) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    induction i using Fin.lastCases with
    | last =>
        simp only [AlgHom.comp_apply, affineRelation, aeval_X, Fin.snoc_last,
          map_mul, aeval_C, MvPolynomial.algebraMap_eq, AlgHom.id_apply]
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hs, map_one, one_mul]
    | cast i =>
        simp only [AlgHom.comp_apply, affineRelation, aeval_X, Fin.snoc_castSucc,
          map_add, map_mul, aeval_C, MvPolynomial.algebraMap_eq, AlgHom.id_apply]
        calc
          _ = C (a i + r * -(r⁻¹ * a i)) + C (r * r⁻¹) * X i.castSucc := by
            simp only [map_add, map_mul, map_neg]
            ring
          _ = X i.castSucc := by simp [hr, ← mul_assoc]
  apply Function.LeftInverse.injective (g := affineRelation (fun i => -(r⁻¹ * a i)) r⁻¹ s⁻¹)
  intro P
  exact congrArg (fun h : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ]
    MvPolynomial (Fin (n + 1)) ℂ => h P) he

lemma totalDegree_affineRelation_le {n : ℕ} (a : Fin n → ℂ) (r s : ℂ)
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    (affineRelation a r s P).totalDegree ≤ P.totalDegree := by
  apply (totalDegree_aeval_le _ (s := 1) ?_ P).trans_eq (one_mul _)
  intro i
  induction i using Fin.lastCases with
  | last =>
      simp only [Fin.snoc_last]
      simpa using totalDegree_mul (C s) (X (Fin.last n))
  | cast i =>
      simp only [Fin.snoc_castSucc]
      apply (totalDegree_add _ _).trans
      apply max_le
      · simp
      · simpa using totalDegree_mul (C r) (X i.castSucc)

end Submission.Obl.k4_algebraic_real_jet_comparison
