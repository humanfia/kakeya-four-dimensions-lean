import Mathlib

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set

/-- Coordinates are `(t, y, v, x, b, c)`, with
`y = a₀ + t v` and `x = a₂ + t b + t² c`. -/
def chartCoefficients (z : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![z 1 - z 0 * z 2, z 2, z 3 - z 0 * z 4 - z 0 ^ 2 * z 5, z 4, z 5]

def unshear (z : Fin 6 → ℝ) : (Fin 5 → ℝ) × ℝ :=
  (chartCoefficients z, z 0)

def scalarShearMatrix (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of ![![1, -t, 0, 0, 0], ![0, 1, 0, 0, 0],
    ![0, 0, 1, -t, -(t ^ 2)], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]

def scalarFibreShear (t : ℝ) (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![z 0 - t * z 1, z 1, z 2 - t * z 3 - t ^ 2 * z 4, z 3, z 4]

theorem scalarShearMatrix_toLin (t : ℝ) (z : Fin 5 → ℝ) :
    Matrix.toLin' (scalarShearMatrix t) z = scalarFibreShear t z := by
  funext i
  rw [Matrix.toLin'_apply]
  fin_cases i <;>
    simp [scalarShearMatrix, scalarFibreShear, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem scalarShearMatrix_det (t : ℝ) : (scalarShearMatrix t).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [scalarShearMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [scalarShearMatrix]

theorem scalarFibreShear_map (t : ℝ) :
    Measure.map (scalarFibreShear t) (volume : Measure (Fin 5 → ℝ)) = volume := by
  have hdet : LinearMap.det (Matrix.toLin' (scalarShearMatrix t)) = 1 := by
    rw [LinearMap.det_toLin', scalarShearMatrix_det]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin 5 → ℝ)) (f := Matrix.toLin' (scalarShearMatrix t))
    (by rw [hdet]; norm_num)
  have hfun : (⇑(Matrix.toLin' (scalarShearMatrix t))) = scalarFibreShear t :=
    funext (scalarShearMatrix_toLin t)
  rw [hfun, hdet] at h
  simpa using h

theorem measurePreserving_unshear :
    MeasurePreserving unshear (volume : Measure (Fin 6 → ℝ))
      ((volume : Measure (Fin 5 → ℝ)).prod (volume : Measure ℝ)) := by
  have htime := volume_preserving_piFinSuccAbove (fun _ : Fin 6 => ℝ) 0
  have hshear : MeasurePreserving
      (fun p : ℝ × (Fin 5 → ℝ) => (id p.1, scalarFibreShear p.1 p.2))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 5 → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 5 → ℝ))) := by
    apply (MeasurePreserving.id volume).skew_product
    · unfold scalarFibreShear
      fun_prop
    · exact Filter.Eventually.of_forall scalarFibreShear_map
  have hswap := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin 5 → ℝ)))
  convert hswap.comp (hshear.comp htime) using 1
  funext z
  simp only [Function.comp_apply, unshear, Prod.swap_prod_mk, id,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
  refine Prod.ext ?_ rfl
  funext i
  fin_cases i <;> simp [chartCoefficients, scalarFibreShear, Fin.removeNth]

def chartEquiv : ((Fin 5 → ℝ) × ℝ) ≃ᵐ (Fin 6 → ℝ) where
  toFun p := ![p.2, p.1 0 + p.2 * p.1 1, p.1 1,
    p.1 2 + p.2 * p.1 3 + p.2 ^ 2 * p.1 4, p.1 3, p.1 4]
  invFun := unshear
  left_inv p := by
    rcases p with ⟨a, t⟩
    refine Prod.ext ?_ rfl
    funext i
    fin_cases i <;> simp [unshear, chartCoefficients] <;> ring
  right_inv z := by
    funext i
    fin_cases i <;> simp [unshear, chartCoefficients] <;> ring
  measurable_toFun := by
    apply Measurable.of_eval
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  measurable_invFun := by
    change Measurable unshear
    exact measurePreserving_unshear.measurable

theorem measurePreserving_chartEquiv :
    MeasurePreserving chartEquiv
      ((volume : Measure (Fin 5 → ℝ)).prod (volume : Measure ℝ))
      (volume : Measure (Fin 6 → ℝ)) :=
  MeasurePreserving.symm chartEquiv.symm measurePreserving_unshear

def join (q : (Fin 2 → ℝ) × (Fin 4 → ℝ)) : Fin 6 → ℝ :=
  ![q.1 0, q.1 1, q.2 0, q.2 1, q.2 2, q.2 3]

theorem measurePreserving_join :
    MeasurePreserving join
      ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure (Fin 4 → ℝ)))
      (volume : Measure (Fin 6 → ℝ)) := by
  have hsplit := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 2 ⊕ Fin 4 => ℝ)
  have hperm := volume_measurePreserving_piCongrLeft (fun _ : Fin (2 + 4) => ℝ)
    (finSumFinEquiv : Fin 2 ⊕ Fin 4 ≃ Fin (2 + 4))
  convert hperm.comp hsplit using 1
  funext q
  funext i
  fin_cases i <;> rfl

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
