-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/SixShear.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). The six-parameter shear behind the two-basis switched endpoint.

The base endpoint of six signed legs is `A δ_I + B δ_J`, with `I` the first
and `J` the last three durations. The shear `δ ↦ (A δ_I + B δ_J, δ_J)` has
determinant `det A`, and the derivative of the pulled-back height in a single
`J` coordinate is the base-cancelling kernel derivative of
`Submission.Lib.K4CubicTests.endpointKernelPolynomial`.
The fiber construction follows the scalar `SwitchEndpoint` of
`Submission.Lib.K4ScalarSwitching` (sessions x0511/x0212).
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.LinearSplit
import Submission.Lib.K4CubicTests.SwitchedSkew
import Submission.Lib.K4PolynomialPotential.Coordinate
import Submission.Lib.K4ScalarSwitching.Switching
import Submission.Lib.K4ScalarSwitching.SwitchPath
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory MvPolynomial Matrix

/-- The first three of six durations. -/
def selI (i : Fin 3) : Fin 6 := ⟨i, by omega⟩

/-- The last three of six durations. -/
def selJ (j : Fin 3) : Fin 6 := ⟨3 + j, by omega⟩

theorem selI_eq (i : Fin 3) : selI i = Fin.castAdd 3 i := rfl

theorem selJ_eq (j : Fin 3) : selJ j = Fin.natAdd 3 j := rfl

/-- Six coordinates as two blocks of three. -/
def sixBlocks : Fin 6 ≃ Fin 3 ⊕ Fin 3 := (finSumFinEquiv (m := 3) (n := 3)).symm

@[simp] theorem sixBlocks_selI (i : Fin 3) : sixBlocks (selI i) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd i

@[simp] theorem sixBlocks_selJ (j : Fin 3) : sixBlocks (selJ j) = Sum.inr j :=
  finSumFinEquiv_symm_apply_natAdd j

theorem sixBlocks_symm_inl (i : Fin 3) : sixBlocks.symm (Sum.inl i) = selI i :=
  finSumFinEquiv_apply_left i

theorem sixBlocks_symm_inr (j : Fin 3) : sixBlocks.symm (Sum.inr j) = selJ j :=
  finSumFinEquiv_apply_right j

theorem sum_six (f : Fin 6 → ℝ) :
    ∑ k, f k = ∑ i : Fin 3, f (selI i) + ∑ j : Fin 3, f (selJ j) := by
  rw [← sixBlocks.symm.sum_comp, Fintype.sum_sum_type]
  simp only [sixBlocks_symm_inl, sixBlocks_symm_inr]

theorem selJ_ne_selI (j i : Fin 3) : selJ j ≠ selI i := by
  intro h
  have := congrArg Fin.val h
  simp only [selJ, selI] at this
  omega

theorem selJ_injective : Function.Injective selJ := by
  intro a b h
  have := congrArg Fin.val h
  simp only [selJ] at this
  exact Fin.ext (by omega)

/-- The shear matrix `[[A, B], [0, 1]]` on six coordinates. -/
noncomputable def sixShearMatrix (A B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  (Matrix.fromBlocks A B 0 1).submatrix sixBlocks sixBlocks

/-- Its inverse `[[Ai, -Ai B], [0, 1]]`. -/
noncomputable def sixShearInvMatrix (Ai B : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  (Matrix.fromBlocks Ai (-(Ai * B)) 0 1).submatrix sixBlocks sixBlocks

theorem sixShearMatrix_det (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    (sixShearMatrix A B).det = A.det := by
  rw [sixShearMatrix, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

theorem sixShear_mul_inv (A Ai B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * Ai = 1) :
    sixShearMatrix A B * sixShearInvMatrix Ai B = 1 := by
  rw [sixShearMatrix, sixShearInvMatrix, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  have hblock : Matrix.fromBlocks (A * Ai + B * 0) (A * -(Ai * B) + B * 1)
      (0 * Ai + 1 * 0) (0 * -(Ai * B) + 1 * 1) =
        (Matrix.fromBlocks 1 0 0 1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) := by
    have h1 : A * -(Ai * B) + B * 1 = 0 := by
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, hA, Matrix.one_mul, Matrix.mul_one,
        neg_add_cancel]
    rw [h1, hA]
    simp
  rw [hblock, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem sixShear_inv_mul (A Ai B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * Ai = 1) :
    sixShearInvMatrix Ai B * sixShearMatrix A B = 1 :=
  mul_eq_one_comm.mp (sixShear_mul_inv A Ai B hA)

/-- The shear as a linear equivalence of the six duration coordinates. -/
noncomputable def sixShear (A Ai B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * Ai = 1) :
    (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (sixShearMatrix A B))
    (Matrix.toLin' (sixShearInvMatrix Ai B))
    (by rw [← Matrix.toLin'_mul, sixShear_mul_inv A Ai B hA, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, sixShear_inv_mul A Ai B hA, Matrix.toLin'_one])

theorem sixShear_apply (A Ai B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * Ai = 1)
    (δ : Fin 6 → ℝ) : sixShear A Ai B hA δ = sixShearMatrix A B *ᵥ δ := rfl

theorem sixShear_det (A Ai B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * Ai = 1) :
    LinearMap.det (sixShear A Ai B hA : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ)) = A.det := by
  change LinearMap.det (Matrix.toLin' (sixShearMatrix A B)) = A.det
  rw [LinearMap.det_toLin', sixShearMatrix_det]

theorem sixShearInv_mulVec_shear (A Ai B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * Ai = 1)
    (δ : Fin 6 → ℝ) : sixShearInvMatrix Ai B *ᵥ (sixShearMatrix A B *ᵥ δ) = δ := by
  rw [Matrix.mulVec_mulVec, sixShear_inv_mul A Ai B hA, Matrix.one_mulVec]

/-- The six-coordinate shear acts as the base endpoint on the first three
coordinates. -/
theorem sixShearMatrix_mulVec_selI (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (δ : Fin 6 → ℝ) (i : Fin 3) :
    (sixShearMatrix A B *ᵥ δ) (selI i) =
      (A *ᵥ (fun k => δ (selI k))) i + (B *ᵥ (fun k => δ (selJ k))) i := by
  rw [sixShearMatrix, Matrix.submatrix_mulVec_equiv, Function.comp_apply, sixBlocks_selI,
    Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inl, Pi.add_apply]
  congr 2

/-- ... and as the identity on the last three coordinates. -/
theorem sixShearMatrix_mulVec_selJ (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (δ : Fin 6 → ℝ) (j : Fin 3) :
    (sixShearMatrix A B *ᵥ δ) (selJ j) = δ (selJ j) := by
  rw [sixShearMatrix, Matrix.submatrix_mulVec_equiv, Function.comp_apply, sixBlocks_selJ,
    Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inr, Matrix.zero_mulVec, zero_add, Matrix.one_mulVec,
    Function.comp_apply, sixBlocks_symm_inr]

/-- The inverse entries in a selected `J` column. -/
theorem sixShearInvMatrix_selI_selJ (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    sixShearInvMatrix Ai B (selI i) (selJ j) = -(Ai * B) i j := by
  simp only [sixShearInvMatrix, Matrix.submatrix_apply, sixBlocks_selI, sixBlocks_selJ,
    Matrix.fromBlocks_apply₁₂, Matrix.neg_apply]

theorem sixShearInvMatrix_selJ_selJ (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    sixShearInvMatrix Ai B (selJ i) (selJ j) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  simp only [sixShearInvMatrix, Matrix.submatrix_apply, sixBlocks_selJ,
    Matrix.fromBlocks_apply₂₂]

/-- Linear forms of the inverse shear, as polynomials. -/
noncomputable def sixShearInvRows (Ai B : Matrix (Fin 3) (Fin 3) ℝ) :
    Fin 6 → MvPolynomial (Fin 6) ℝ :=
  fun k => ∑ l, C (sixShearInvMatrix Ai B k l) * X l

theorem eval_sixShearInvRows (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 6 → ℝ) :
    (fun k => eval x (sixShearInvRows Ai B k)) = sixShearInvMatrix Ai B *ᵥ x := by
  funext k
  simp [sixShearInvRows, Matrix.mulVec, dotProduct]

theorem pderiv_sixShearInvRows (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (k p : Fin 6) :
    pderiv p (sixShearInvRows Ai B k) = C (sixShearInvMatrix Ai B k p) := by
  classical
  simp only [sixShearInvRows, map_sum, Derivation.leibniz, pderiv_C, pderiv_X, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

theorem sixShearInvRows_degree (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 6) :
    (sixShearInvRows Ai B k).totalDegree ≤ 1 := by
  unfold sixShearInvRows
  apply totalDegree_finsetSum_le
  intro l _
  exact (totalDegree_mul _ _).trans (by simp)

/-- The height in sheared coordinates. -/
noncomputable def shearPullback (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (H : MvPolynomial (Fin 6) ℝ) :
    MvPolynomial (Fin 6) ℝ :=
  aeval (sixShearInvRows Ai B) H

theorem eval_shearPullback (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (H : MvPolynomial (Fin 6) ℝ)
    (x : Fin 6 → ℝ) :
    eval x (shearPullback Ai B H) = eval (sixShearInvMatrix Ai B *ᵥ x) H := by
  rw [shearPullback, Submission.Lib.K4ScalarSwitching.Switching.eval_substitution,
    eval_sixShearInvRows]

theorem shearPullback_degree (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (H : MvPolynomial (Fin 6) ℝ) :
    (shearPullback Ai B H).totalDegree ≤ H.totalDegree :=
  Submission.Lib.K4ScalarSwitching.PolynomialDegree.degree_aeval_le H _
    (sixShearInvRows_degree Ai B)

/-- The derivative of the sheared height in the selected `J` coordinate is
the base-cancelling kernel derivative. -/
theorem eval_pderiv_shearPullback (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (H : MvPolynomial (Fin 6) ℝ)
    (j : Fin 3) (x : Fin 6 → ℝ) :
    eval x (pderiv (selJ j) (shearPullback Ai B H)) =
      eval (sixShearInvMatrix Ai B *ᵥ x)
        (Submission.Lib.K4CubicTests.endpointKernelPolynomial H Ai B selI selJ j) := by
  rw [shearPullback, Submission.Lib.K4ScalarSwitching.Switching.partial_aeval]
  simp only [pderiv_sixShearInvRows, map_sum, map_mul, eval_C,
    Submission.Lib.K4ScalarSwitching.Switching.eval_substitution, eval_sixShearInvRows]
  rw [sum_six]
  simp only [sixShearInvMatrix_selI_selJ, sixShearInvMatrix_selJ_selJ,
    Submission.Lib.K4CubicTests.endpointKernelPolynomial, map_sub, map_sum, map_mul, eval_C]
  rw [Finset.sum_eq_single (f := fun k : Fin 3 => eval (sixShearInvMatrix Ai B *ᵥ x)
      (pderiv (selJ k) H) * (1 : Matrix (Fin 3) (Fin 3) ℝ) k j) j]
  · simp only [Matrix.one_apply_eq, mul_one]
    rw [sub_eq_neg_add, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro k _ hk
    simp [hk]
  · simp

/-- The univariate fiber polynomial in the selected `J` coordinate. -/
noncomputable def shearFiber (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (H : MvPolynomial (Fin 6) ℝ)
    (j : Fin 3) (x : Fin 5 → ℝ) : Polynomial ℝ :=
  Submission.Lib.K4PolynomialPotential.coordinatePolynomialHom
    (Fin.insertNth (α := fun _ => ℝ) (selJ j) 0 x) (selJ j) (shearPullback Ai B H)

theorem eval_shearFiber (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (H : MvPolynomial (Fin 6) ℝ)
    (j : Fin 3) (x : Fin 5 → ℝ) (s : ℝ) :
    (shearFiber Ai B H j x).eval s =
      eval (Fin.insertNth (α := fun _ => ℝ) (selJ j) s x) (shearPullback Ai B H) := by
  rw [shearFiber, Submission.Lib.K4PolynomialPotential.eval_coordinatePolynomialHom,
    Fin.update_insertNth]

theorem derivative_shearFiber (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (H : MvPolynomial (Fin 6) ℝ)
    (j : Fin 3) (x : Fin 5 → ℝ) (s : ℝ) :
    (shearFiber Ai B H j x).derivative.eval s =
      eval (Fin.insertNth (α := fun _ => ℝ) (selJ j) s x)
        (pderiv (selJ j) (shearPullback Ai B H)) := by
  rw [shearFiber, Submission.Lib.K4PolynomialPotential.derivative_coordinatePolynomialHom,
    Submission.Lib.K4PolynomialPotential.eval_coordinatePolynomialHom, Fin.update_insertNth]

theorem shearFiber_degree (Ai B : Matrix (Fin 3) (Fin 3) ℝ) (H : MvPolynomial (Fin 6) ℝ)
    (j : Fin 3) (x : Fin 5 → ℝ) :
    (shearFiber Ai B H j x).natDegree ≤ H.totalDegree := by
  apply Nat.le_trans _ (shearPullback_degree Ai B H)
  change (MvPolynomial.aeval
      (fun k => if k = selJ j then Polynomial.X
        else Polynomial.C ((Fin.insertNth (α := fun _ => ℝ) (selJ j) 0 x) k))
      (shearPullback Ai B H)).natDegree ≤ (shearPullback Ai B H).totalDegree
  simpa only [Nat.mul_one] using
    MvPolynomial.aeval_natDegree_le (n := 1) (shearPullback Ai B H) le_rfl _
      (fun k => by split_ifs <;> simp)

end Submission.Obl.k4_physical_row_packet_potential.Switch
