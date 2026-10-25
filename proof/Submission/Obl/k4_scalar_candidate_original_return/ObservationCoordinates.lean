import Submission.Obl.k4_scalar_candidate_original_return.CoordinateFormat

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory MvPolynomial

noncomputable section

/-- Both observed positions are coordinates; the hidden bin then depends on
one fiber coordinate and is constant when the base is averaged. -/
def observedCoefficient (t : ℝ) (a : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![a 0 + t * a 1, a 1, a 2 + t * a 3 + t ^ 2 * a 4, a 3, a 4]

def unobservedCoefficient (t : ℝ) (a : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![a 0 - t * a 1, a 1, a 2 - t * a 3 - t ^ 2 * a 4, a 3, a 4]

private lemma measurePreserving_transvection (i j : Fin 5) (hij : i ≠ j) (t : ℝ) :
    MeasurePreserving (Matrix.toLin' (Matrix.transvection i j t))
      (volume : Measure (Fin 5 → ℝ)) volume := by
  have hdet := Matrix.det_transvection_of_ne i j hij t
  refine ⟨(Matrix.toLin' (Matrix.transvection i j t)).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [hdet]; norm_num), hdet]
  simp

private lemma transvection23_apply (t : ℝ) (a : Fin 5 → ℝ) :
    Matrix.toLin' (Matrix.transvection (2 : Fin 5) 3 t) a =
      ![a 0, a 1, a 2 + t * a 3, a 3, a 4] := by
  funext i
  rw [Matrix.toLin'_apply]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.transvection,
      Matrix.single, Matrix.one_apply]

private lemma transvection24_apply (t : ℝ) (a : Fin 5 → ℝ) :
    Matrix.toLin' (Matrix.transvection (2 : Fin 5) 4 t) a =
      ![a 0, a 1, a 2 + t * a 4, a 3, a 4] := by
  funext i
  rw [Matrix.toLin'_apply]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.transvection,
      Matrix.single, Matrix.one_apply]

lemma observedCoefficient_comp (t : ℝ) : observedCoefficient t =
    (Matrix.toLin' (Matrix.transvection (2 : Fin 5) 4 (t ^ 2))) ∘
    (Matrix.toLin' (Matrix.transvection (2 : Fin 5) 3 t)) ∘ shearCoefficient t := by
  funext a
  simp only [Function.comp_apply, transvection24_apply, transvection23_apply]
  funext i
  fin_cases i <;> simp [shearCoefficient, observedCoefficient]

lemma measurePreserving_observedCoefficient (t : ℝ) :
    MeasurePreserving (observedCoefficient t) (volume : Measure (Fin 5 → ℝ)) volume := by
  rw [observedCoefficient_comp]
  exact (measurePreserving_transvection 2 4 (by decide) (t ^ 2)).comp
    ((measurePreserving_transvection 2 3 (by decide) t).comp (measurePreserving_shearCoefficient t))

lemma measurable_observedCoefficient :
    Measurable (fun p : ℝ × (Fin 5 → ℝ) => observedCoefficient p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [observedCoefficient] <;> fun_prop

lemma measurable_unobservedCoefficient :
    Measurable (fun p : ℝ × (Fin 5 → ℝ) => unobservedCoefficient p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [unobservedCoefficient] <;> fun_prop

def observedSkew : ℝ × (Fin 5 → ℝ) ≃ᵐ ℝ × (Fin 5 → ℝ) where
  toFun p := (p.1, observedCoefficient p.1 p.2)
  invFun p := (p.1, unobservedCoefficient p.1 p.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [observedCoefficient, unobservedCoefficient] <;> ring
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [observedCoefficient, unobservedCoefficient] <;> ring
  measurable_toFun := measurable_fst.prodMk measurable_observedCoefficient
  measurable_invFun := measurable_fst.prodMk measurable_unobservedCoefficient

lemma measurePreserving_observedSkew :
    MeasurePreserving observedSkew ((volume : Measure ℝ).prod (volume : Measure (Fin 5 → ℝ)))
      (volume.prod volume) := by
  exact (MeasurePreserving.id (volume : Measure ℝ)).skew_product measurable_observedCoefficient
    (Filter.Eventually.of_forall fun t => (measurePreserving_observedCoefficient t).map_eq)

/-- Coordinates `(t,y,a₁,x,a₃,a₄)` retain two exact base coordinates and four
hidden fiber coordinates, including the original hidden observation. -/
def observationShear : (Fin 5 → ℝ) × ℝ ≃ᵐ (Fin 6 → ℝ) :=
  MeasurableEquiv.prodComm.trans
    (observedSkew.trans (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 6 => ℝ) 0).symm)

lemma observationShear_apply (a : Fin 5 → ℝ) (t : ℝ) :
    observationShear (a, t) =
      ![t, a 0 + t * a 1, a 1, a 2 + t * a 3 + t ^ 2 * a 4, a 3, a 4] := by
  funext i
  fin_cases i <;> rfl

lemma observationShear_symm_apply (w : Fin 6 → ℝ) :
    observationShear.symm w =
      (![w 1 - w 0 * w 2, w 2, w 3 - w 0 * w 4 - w 0 ^ 2 * w 5, w 4, w 5], w 0) := by
  apply observationShear.injective
  rw [MeasurableEquiv.apply_symm_apply, observationShear_apply]
  funext i
  fin_cases i <;> simp <;> ring

lemma measurePreserving_observationShear :
    MeasurePreserving observationShear ((volume : Measure (Fin 5 → ℝ)).prod (volume : Measure ℝ))
      (volume : Measure (Fin 6 → ℝ)) := by
  exact ((volume_preserving_piFinSuccAbove (fun _ : Fin 6 => ℝ) 0).symm _).comp
    (measurePreserving_observedSkew.comp Measure.measurePreserving_swap)

end

end Submission.Obl.k4_scalar_candidate_original_return
