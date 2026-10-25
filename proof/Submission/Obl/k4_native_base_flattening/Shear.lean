import Mathlib

/-!
# Sheared coordinates

A native line with coefficients `x` at time `t` is described in sheared coordinates
`(t, y₁, y₂, w, s₁, s₂, s₃)` with `y₁ = x₀ + t x₃`, `y₂ = x₁ + t x₄`, `w = x₂ + t x₅` and
`(s₁, s₂, s₃) = (x₃, x₄, x₅)`. The change of variables is triangular with determinant one, so it
preserves volume: over each time it is a unipotent linear map of the coefficients.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_native_base_flattening

/-- Native coefficients of a point in sheared coordinates `(t, y₁, y₂, w, s₁, s₂, s₃)`. -/
def coeffs (s : Fin 7 → ℝ) : Fin 6 → ℝ :=
  ![s 1 - s 0 * s 4, s 2 - s 0 * s 5, s 3 - s 0 * s 6, s 4, s 5, s 6]

/-- Sheared coordinates to the native pair (coefficients, time). -/
def unshear (s : Fin 7 → ℝ) : (Fin 6 → ℝ) × ℝ := (coeffs s, s 0)

/-- The fibre shear at time `t`, as a matrix. -/
def shearMatrix (t : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of ![![1, 0, 0, -t, 0, 0], ![0, 1, 0, 0, -t, 0], ![0, 0, 1, 0, 0, -t],
    ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

/-- The fibre shear at time `t`. -/
def fibreShear (t : ℝ) (y : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![y 0 - t * y 3, y 1 - t * y 4, y 2 - t * y 5, y 3, y 4, y 5]

lemma toLin'_shearMatrix (t : ℝ) (y : Fin 6 → ℝ) :
    Matrix.toLin' (shearMatrix t) y = fibreShear t y := by
  funext i
  rw [Matrix.toLin'_apply]
  fin_cases i <;>
    simp [shearMatrix, fibreShear, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

lemma det_shearMatrix (t : ℝ) : (shearMatrix t).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [shearMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [shearMatrix]

lemma map_fibreShear (t : ℝ) :
    Measure.map (fibreShear t) (volume : Measure (Fin 6 → ℝ)) = volume := by
  have hdet : LinearMap.det (Matrix.toLin' (shearMatrix t)) = 1 := by
    rw [LinearMap.det_toLin', det_shearMatrix]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin 6 → ℝ))
    (f := Matrix.toLin' (shearMatrix t)) (by rw [hdet]; norm_num)
  have hfun : (⇑(Matrix.toLin' (shearMatrix t))) = fibreShear t := by
    funext y; exact toLin'_shearMatrix t y
  rw [hfun] at h
  rw [h, hdet]
  simp

theorem measurePreserving_unshear :
    MeasurePreserving unshear (volume : Measure (Fin 7 → ℝ))
      ((volume : Measure (Fin 6 → ℝ)).prod (volume : Measure ℝ)) := by
  have h0 := volume_preserving_piFinSuccAbove (fun _ : Fin 7 => ℝ) 0
  have h1 : MeasurePreserving (fun p : ℝ × (Fin 6 → ℝ) => (id p.1, fibreShear p.1 p.2))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 6 → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 6 → ℝ))) := by
    refine (MeasurePreserving.id volume).skew_product ?_ ?_
    · unfold fibreShear
      fun_prop
    · exact Filter.Eventually.of_forall map_fibreShear
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin 6 → ℝ))))
  have h := h2.comp (h1.comp h0)
  convert h using 1
  funext s
  simp only [Function.comp_apply, unshear, Prod.swap_prod_mk, id]
  simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
  refine Prod.ext ?_ rfl
  funext i
  fin_cases i <;> simp [coeffs, fibreShear, Fin.removeNth]

/-- Joins base and transverse sheared coordinates. -/
def join (q : (Fin 3 → ℝ) × (Fin 4 → ℝ)) : Fin 7 → ℝ :=
  ![q.1 0, q.1 1, q.1 2, q.2 0, q.2 1, q.2 2, q.2 3]

theorem measurePreserving_join :
    MeasurePreserving join ((volume : Measure (Fin 3 → ℝ)).prod (volume : Measure (Fin 4 → ℝ)))
      (volume : Measure (Fin 7 → ℝ)) := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 3 ⊕ Fin 4 => ℝ)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : Fin (3 + 4) => ℝ)
    (finSumFinEquiv : Fin 3 ⊕ Fin 4 ≃ Fin (3 + 4))
  have h := h2.comp h1
  convert h using 1
  funext q
  funext i
  fin_cases i <;> rfl

lemma measurable_join : Measurable join := measurePreserving_join.measurable

/-- Product sheared coordinates to the native pair (coefficients, time). -/
def native (q : (Fin 3 → ℝ) × (Fin 4 → ℝ)) : (Fin 6 → ℝ) × ℝ := unshear (join q)

theorem measurePreserving_native :
    MeasurePreserving native ((volume : Measure (Fin 3 → ℝ)).prod (volume : Measure (Fin 4 → ℝ)))
      ((volume : Measure (Fin 6 → ℝ)).prod (volume : Measure ℝ)) :=
  measurePreserving_unshear.comp measurePreserving_join

lemma measurable_native : Measurable native := measurePreserving_native.measurable

end Submission.Obl.k4_native_base_flattening
