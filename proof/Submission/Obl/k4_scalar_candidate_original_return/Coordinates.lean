import Submission.Obl.k4_scalar_candidate_original_return.Defs

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory

noncomputable section

/-- At fixed time only the spatial intercept is sheared. -/
def shearCoefficient (t : ℝ) (a : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![a 0 + t * a 1, a 1, a 2, a 3, a 4]

lemma shearCoefficient_matrix (t : ℝ) (a : Fin 5 → ℝ) :
    Matrix.toLin' (Matrix.transvection (0 : Fin 5) 1 t) a = shearCoefficient t a := by
  funext i
  rw [Matrix.toLin'_apply]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.transvection,
      Matrix.single, Matrix.one_apply, shearCoefficient]

lemma shearCoefficient_neg (t : ℝ) (a : Fin 5 → ℝ) :
    shearCoefficient (-t) (shearCoefficient t a) = a := by
  funext i
  fin_cases i <;> simp [shearCoefficient]

lemma shearCoefficient_neg_right (t : ℝ) (a : Fin 5 → ℝ) :
    shearCoefficient t (shearCoefficient (-t) a) = a := by
  simpa only [neg_neg] using shearCoefficient_neg (-t) a

lemma measurable_shearCoefficient :
    Measurable (fun p : ℝ × (Fin 5 → ℝ) => shearCoefficient p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [shearCoefficient] <;> fun_prop

lemma measurePreserving_shearCoefficient (t : ℝ) :
    MeasurePreserving (shearCoefficient t) (volume : Measure (Fin 5 → ℝ)) volume := by
  have hdet : (Matrix.transvection (0 : Fin 5) 1 t).det = 1 :=
    Matrix.det_transvection_of_ne (0 : Fin 5) 1 (by decide) t
  have hfun : shearCoefficient t = ⇑(Matrix.toLin' (Matrix.transvection (0 : Fin 5) 1 t)) :=
    funext fun a => (shearCoefficient_matrix t a).symm
  refine ⟨measurable_shearCoefficient.comp (measurable_const.prodMk measurable_id), ?_⟩
  rw [hfun, Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [hdet]; norm_num), hdet]
  simp

/-- The triangular coefficient shear, retaining time. -/
def scalarSkew : ℝ × (Fin 5 → ℝ) ≃ᵐ ℝ × (Fin 5 → ℝ) where
  toFun p := (p.1, shearCoefficient p.1 p.2)
  invFun p := (p.1, shearCoefficient (-p.1) p.2)
  left_inv p := by simp [shearCoefficient_neg]
  right_inv p := by simp [shearCoefficient_neg_right]
  measurable_toFun := measurable_fst.prodMk measurable_shearCoefficient
  measurable_invFun := measurable_fst.prodMk
    (measurable_shearCoefficient.comp (measurable_fst.neg.prodMk measurable_snd))

lemma measurePreserving_scalarSkew :
    MeasurePreserving scalarSkew ((volume : Measure ℝ).prod (volume : Measure (Fin 5 → ℝ)))
      (volume.prod volume) := by
  exact (MeasurePreserving.id (volume : Measure ℝ)).skew_product measurable_shearCoefficient
    (Filter.Eventually.of_forall fun t => (measurePreserving_shearCoefficient t).map_eq)

/-- Coordinates `(t,y,a₁,a₂,a₃,a₄)`, before marginalizing the four hidden coefficients. -/
def scalarShear : (Fin 5 → ℝ) × ℝ ≃ᵐ (Fin 6 → ℝ) :=
  MeasurableEquiv.prodComm.trans
    (scalarSkew.trans (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 6 => ℝ) 0).symm)

lemma scalarShear_apply (a : Fin 5 → ℝ) (t : ℝ) :
    scalarShear (a, t) = ![t, a 0 + t * a 1, a 1, a 2, a 3, a 4] := by
  funext i
  fin_cases i <;> rfl

lemma scalarShear_symm_apply (z : Fin 6 → ℝ) :
    scalarShear.symm z = (![z 1 - z 0 * z 2, z 2, z 3, z 4, z 5], z 0) := by
  apply scalarShear.injective
  rw [MeasurableEquiv.apply_symm_apply, scalarShear_apply]
  funext i
  fin_cases i <;> simp

lemma measurePreserving_scalarShear :
    MeasurePreserving scalarShear ((volume : Measure (Fin 5 → ℝ)).prod (volume : Measure ℝ))
      (volume : Measure (Fin 6 → ℝ)) := by
  exact ((volume_preserving_piFinSuccAbove (fun _ : Fin 6 => ℝ) 0).symm _).comp
    (measurePreserving_scalarSkew.comp Measure.measurePreserving_swap)

/-- Separate the observed base from the four hidden coefficients. -/
def scalarSplit : (Fin 6 → ℝ) ≃ᵐ Base × (Fin 4 → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 + 4) => ℝ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 4 => ℝ))

lemma scalarSplit_apply (z : Fin 6 → ℝ) :
    scalarSplit z = (![z 0, z 1], ![z 2, z 3, z 4, z 5]) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

lemma scalarSplit_symm_apply (z : Base × (Fin 4 → ℝ)) :
    scalarSplit.symm z = ![z.1 0, z.1 1, z.2 0, z.2 1, z.2 2, z.2 3] := by
  apply scalarSplit.injective
  rw [MeasurableEquiv.apply_symm_apply, scalarSplit_apply]
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

lemma measurePreserving_scalarSplit :
    MeasurePreserving scalarSplit (volume : Measure (Fin 6 → ℝ))
      ((volume : Measure Base).prod (volume : Measure (Fin 4 → ℝ))) := by
  exact (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 4 => ℝ)).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin (2 + 4) => ℝ) finSumFinEquiv).symm _)

end

end Submission.Obl.k4_scalar_candidate_original_return
