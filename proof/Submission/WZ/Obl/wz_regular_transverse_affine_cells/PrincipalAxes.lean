-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.PrincipalAxes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module Set

lemma real_det_adjoint (A : E →ₗ[ℝ] E) : LinearMap.det A.adjoint = LinearMap.det A := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [← LinearMap.det_toMatrix e.toBasis, LinearMap.toMatrix_adjoint e e,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix]
  rfl

/-- Principal axes of an invertible linear image of a Euclidean ball. The half-widths
are positive, ordered, and their product is the absolute determinant. -/
lemma exists_principal_axes (A : E ≃ₗ[ℝ] E) :
    ∃ (u : OrthonormalBasis (Fin 3) ℝ E) (d : Fin 3 → ℝ),
      (∀ i, 0 < d i) ∧ Antitone d ∧
      (∀ q i, |inner ℝ (u i) (A q)| ≤ d i * ‖q‖) ∧
      (∏ i, d i) = |LinearMap.det (A : E →ₗ[ℝ] E)| ∧
      (∀ i, ∃ q : E, ‖q‖ = 1 ∧ inner ℝ (u i) (A q) = d i) := by
  classical
  let L : E →ₗ[ℝ] E := A
  let G : E →ₗ[ℝ] E := L.comp L.adjoint
  have hG : G.IsSymmetric := LinearMap.isSymmetric_self_comp_adjoint L
  have hdim : Module.finrank ℝ E = 3 := by simp [E]
  let u := hG.eigenvectorBasis hdim
  let d : Fin 3 → ℝ := fun i => ‖L.adjoint (u i)‖
  have hd : ∀ i, 0 < d i := by
    intro i
    apply norm_pos_iff.mpr
    intro hz
    have hi := L.adjoint_inner_left (A.symm (u i)) (u i)
    rw [hz, inner_zero_left] at hi
    have he : L (A.symm (u i)) = u i := A.apply_symm_apply _
    rw [he, real_inner_self_eq_norm_sq, u.norm_eq_one] at hi
    norm_num at hi
  have heigen (i : Fin 3) : (d i) ^ 2 = hG.eigenvalues hdim i := by
    have h := congrArg (fun q => inner ℝ (u i) q) (hG.apply_eigenvectorBasis hdim i)
    change inner ℝ (u i) (L (L.adjoint (u i))) =
      inner ℝ (u i) ((hG.eigenvalues hdim i) • u i) at h
    rw [← LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
      real_inner_smul_right, real_inner_self_eq_norm_sq, u.norm_eq_one] at h
    simpa only [one_pow, mul_one] using h
  refine ⟨u, d, hd, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h := hG.eigenvalues_antitone hdim hij
    rw [← heigen i, ← heigen j] at h
    exact le_of_sq_le_sq h (hd i).le
  · intro q i
    change |inner ℝ (u i) (L q)| ≤ d i * ‖q‖
    rw [← L.adjoint_inner_left]
    exact abs_real_inner_le_norm _ _
  · have hsq : (∏ i, d i) ^ 2 = (LinearMap.det L) ^ 2 := by
      calc (∏ i, d i) ^ 2 = ∏ i, (d i) ^ 2 := (Finset.prod_pow _ _ _).symm
        _ = ∏ i, hG.eigenvalues hdim i := Finset.prod_congr rfl fun i _ => heigen i
        _ = LinearMap.det G := (hG.det_eq_prod_eigenvalues hdim).symm
        _ = (LinearMap.det L) ^ 2 := by rw [LinearMap.det_comp, real_det_adjoint]; ring
    apply (sq_eq_sq₀ (Finset.prod_nonneg fun i _ => (hd i).le) (abs_nonneg (LinearMap.det L))).mp
    simpa only [sq_abs] using hsq
  · intro i
    refine ⟨(d i)⁻¹ • L.adjoint (u i), ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hd i))]
      change (d i)⁻¹ * d i = 1
      exact inv_mul_cancel₀ (hd i).ne'
    · change inner ℝ (u i) (L ((d i)⁻¹ • L.adjoint (u i))) = d i
      rw [← L.adjoint_inner_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      change (d i)⁻¹ * (d i) ^ 2 = d i
      field_simp

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
