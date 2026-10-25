-- Copied from LOT tree oai_074_kakeya_four_dimensions, obligation o075 (k4_joint_homogenization),
-- branch x0254, file Submission/Obl/k4_joint_homogenization/Shear.lean (session x0254's own proofs), renamed into this namespace.
import Mathlib

/-!
# Sheared trajectory coordinates

A trajectory `x = (b₁, b₂, b₃, s₁, s₂, s₃)` at time `t` is recorded in the coordinates
`z = (t, b₁ + t s₁, b₂ + t s₂, b₃ + t s₃, s₁, s₂, s₃)`: the base point `(t, y(t))`, the hidden
coordinate `w(t)`, and the slope. The change of variables has Jacobian one, so it carries
`volume ⊗ volume` on `ℝ⁶ × ℝ` to `volume` on `ℝ⁷`. The second equivalence splits `ℝ⁷` into the
base `ℝ³` (as Euclidean space) and the fiber `ℝ⁴`, again preserving volume.
-/

namespace Submission.Obl.k4_native_shear_source_transport

open MeasureTheory

/-- The unipotent matrix of the shear `x ↦ (x₀ + t x₃, x₁ + t x₄, x₂ + t x₅, x₃, x₄, x₅)`. -/
noncomputable def shearMatrix (t : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => if i = j then 1 else if (j : ℕ) = (i : ℕ) + 3 then t else 0

theorem shearMatrix_det (t : ℝ) : (shearMatrix t).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [shearMatrix]
  · intro i j hij
    have h1 : i ≠ j := fun h => (lt_irrefl _ (h ▸ hij))
    have h2 : (j : ℕ) ≠ (i : ℕ) + 3 := by
      have : (j : ℕ) < i := hij
      omega
    simp [shearMatrix, h1, h2]

/-- The shear of the coefficient vector at time `t`. -/
def shearVec (t : ℝ) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![x 0 + t * x 3, x 1 + t * x 4, x 2 + t * x 5, x 3, x 4, x 5]

theorem shearMatrix_mulVec (t : ℝ) (x : Fin 6 → ℝ) :
    Matrix.mulVec (shearMatrix t) x = shearVec t x := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, shearMatrix, shearVec]

theorem shearVec_shearVec_neg (t : ℝ) (x : Fin 6 → ℝ) : shearVec (-t) (shearVec t x) = x := by
  funext i
  fin_cases i <;> simp [shearVec]

theorem shearVec_neg_shearVec (t : ℝ) (x : Fin 6 → ℝ) : shearVec t (shearVec (-t) x) = x := by
  funext i
  fin_cases i <;> simp [shearVec]

theorem measurable_shearVec_uncurry :
    Measurable (fun p : ℝ × (Fin 6 → ℝ) => shearVec p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [shearVec] <;> fun_prop

theorem measurePreserving_shearVec (t : ℝ) :
    MeasurePreserving (shearVec t) (volume : Measure (Fin 6 → ℝ)) volume := by
  have hfun : shearVec t = ⇑(Matrix.toLin' (shearMatrix t)) := by
    funext x
    rw [Matrix.toLin'_apply, shearMatrix_mulVec]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (Matrix.toLin' (shearMatrix t)).continuous_of_finiteDimensional.measurable
  · rw [hfun, Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [shearMatrix_det]; norm_num),
      shearMatrix_det]
    simp

/-- The skew product `(t, x) ↦ (t, shearVec t x)`. -/
noncomputable def skewEquiv : ℝ × (Fin 6 → ℝ) ≃ᵐ ℝ × (Fin 6 → ℝ) where
  toFun p := (p.1, shearVec p.1 p.2)
  invFun p := (p.1, shearVec (-p.1) p.2)
  left_inv p := by simp [shearVec_shearVec_neg]
  right_inv p := by simp [shearVec_neg_shearVec]
  measurable_toFun := measurable_fst.prodMk measurable_shearVec_uncurry
  measurable_invFun := measurable_fst.prodMk
    (measurable_shearVec_uncurry.comp (measurable_fst.neg.prodMk measurable_snd))

theorem measurePreserving_skewEquiv :
    MeasurePreserving skewEquiv
      ((volume : Measure ℝ).prod (volume : Measure (Fin 6 → ℝ))) (volume.prod volume) := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun t x => shearVec t x) (μc := (volume : Measure (Fin 6 → ℝ)))
    (μd := (volume : Measure (Fin 6 → ℝ)))
    (measurable_shearVec_uncurry.comp measurable_id)
    (Filter.Eventually.of_forall fun t => (measurePreserving_shearVec t).map_eq)
  exact h

/-- Sheared coordinates `(x, t) ↦ (t, x₀ + t x₃, x₁ + t x₄, x₂ + t x₅, x₃, x₄, x₅)`. -/
noncomputable def shearEquiv : (Fin 6 → ℝ) × ℝ ≃ᵐ (Fin 7 → ℝ) :=
  MeasurableEquiv.prodComm.trans
    (skewEquiv.trans (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 7 => ℝ) 0).symm)

theorem shearEquiv_apply (x : Fin 6 → ℝ) (t : ℝ) :
    shearEquiv (x, t) = ![t, x 0 + t * x 3, x 1 + t * x 4, x 2 + t * x 5, x 3, x 4, x 5] := by
  funext i
  fin_cases i <;> rfl

theorem shearEquiv_symm_apply (z : Fin 7 → ℝ) :
    shearEquiv.symm z =
      (![z 1 - z 0 * z 4, z 2 - z 0 * z 5, z 3 - z 0 * z 6, z 4, z 5, z 6], z 0) := by
  apply shearEquiv.injective
  rw [MeasurableEquiv.apply_symm_apply, shearEquiv_apply]
  funext i
  fin_cases i <;> simp

theorem measurePreserving_shearEquiv :
    MeasurePreserving shearEquiv ((volume : Measure (Fin 6 → ℝ)).prod (volume : Measure ℝ))
      (volume : Measure (Fin 7 → ℝ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodComm : (Fin 6 → ℝ) × ℝ ≃ᵐ ℝ × (Fin 6 → ℝ))
      ((volume : Measure (Fin 6 → ℝ)).prod (volume : Measure ℝ)) (volume.prod volume) :=
    Measure.measurePreserving_swap
  have h3 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 7 => ℝ) 0).symm
      ((volume : Measure ℝ).prod (volume : Measure (Fin 6 → ℝ))) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 7 => ℝ) 0).symm _
  exact h3.comp (measurePreserving_skewEquiv.comp h1)

/-- Base/fiber split `z ↦ ((z₀, z₁, z₂), (z₃, z₄, z₅, z₆))` of the sheared coordinates. -/
noncomputable def baseFiberEquiv : (Fin 7 → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 3) × (Fin 4 → ℝ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin (3 + 4) => ℝ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 4 => ℝ))).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) (MeasurableEquiv.refl _))

theorem baseFiberEquiv_apply (z : Fin 7 → ℝ) :
    baseFiberEquiv z = (WithLp.toLp 2 ![z 0, z 1, z 2], ![z 3, z 4, z 5, z 6]) := by
  have h1 : ∀ i : Fin 3, (baseFiberEquiv z).1.ofLp i = ![z 0, z 1, z 2] i := by
    intro i
    fin_cases i <;> rfl
  have h2 : ∀ i : Fin 4, (baseFiberEquiv z).2 i = ![z 3, z 4, z 5, z 6] i := by
    intro i
    fin_cases i <;> rfl
  ext i
  · exact h1 i
  · exact h2 i

theorem measurePreserving_baseFiberEquiv :
    MeasurePreserving baseFiberEquiv (volume : Measure (Fin 7 → ℝ))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (Fin 4 → ℝ))) := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (3 + 4) => ℝ) finSumFinEquiv).symm
      volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (3 + 4) => ℝ) finSumFinEquiv).symm _
  have h2 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 4 => ℝ))
      volume ((volume : Measure (Fin 3 → ℝ)).prod (volume : Measure (Fin 4 → ℝ))) :=
    volume_measurePreserving_sumPiEquivProdPi _
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        (MeasurableEquiv.refl (Fin 4 → ℝ)))
      ((volume : Measure (Fin 3 → ℝ)).prod (volume : Measure (Fin 4 → ℝ)))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (Fin 4 → ℝ))) :=
    (PiLp.volume_preserving_toLp (Fin 3)).prod (MeasurePreserving.id _)
  exact h3.comp (h2.comp h1)

end Submission.Obl.k4_native_shear_source_transport
