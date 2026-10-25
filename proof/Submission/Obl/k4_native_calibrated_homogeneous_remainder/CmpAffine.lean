import Mathlib
set_option autoImplicit false

/-! Affine chart normalization of the continuous observation coordinates
`(t, y) ↦ ((t - t₀) D, Q⁻¹ (y - c - t u))` and its Lebesgue scaling. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp

open MeasureTheory Set
open scoped ENNReal

/-- The linear part of the chart normalization, as a `3 × 3` matrix. -/
noncomputable def chartMatrix (D : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![D, 0, 0;
    -(Q⁻¹ 0 0 * u 0 + Q⁻¹ 0 1 * u 1), Q⁻¹ 0 0, Q⁻¹ 0 1;
    -(Q⁻¹ 1 0 * u 0 + Q⁻¹ 1 1 * u 1), Q⁻¹ 1 0, Q⁻¹ 1 1]

theorem det_chartMatrix (D : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : (chartMatrix D u Q).det = D * Q⁻¹.det := by
  rw [chartMatrix, Matrix.det_fin_three, Matrix.det_fin_two]
  simp
  ring

/-- The chart normalization of the continuous observation coordinates. -/
noncomputable def chartAff (D t₀ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (w : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(w 0 - t₀) * D,
    (Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![w 1, w 2] - c - w 0 • u)) 0,
    (Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![w 1, w 2] - c - w 0 • u)) 1]

/-- The translation part of the chart normalization. -/
noncomputable def chartShift (D t₀ : ℝ) (c : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![-(t₀ * D), -(Q⁻¹ 0 0 * c 0 + Q⁻¹ 0 1 * c 1),
    -(Q⁻¹ 1 0 * c 0 + Q⁻¹ 1 1 * c 1)]

theorem toEuclideanLin_apply_two (M : Matrix (Fin 2) (Fin 2) ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    Matrix.toEuclideanLin M z i = M i 0 * z 0 + M i 1 * z 1 := by
  simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem chartAff_eq (D t₀ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (w : EuclideanSpace ℝ (Fin 3)) :
    chartAff D t₀ c u Q w =
      Matrix.toEuclideanLin (chartMatrix D u Q) w + chartShift D t₀ c Q := by
  ext i
  fin_cases i <;>
    simp [chartAff, chartShift, chartMatrix, toEuclideanLin_apply_two,
      Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem det_toEuclideanLin {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : LinearMap.det (Matrix.toEuclideanLin M) = M.det := by
  unfold Matrix.toEuclideanLin
  simp

/-- Lebesgue measure under the chart normalization. -/
theorem map_chartAff_volume {D t₀ : ℝ} (hD : 0 < D) (c u : EuclideanSpace ℝ (Fin 2))
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    Measure.map (chartAff D t₀ c u Q) (volume : Measure (EuclideanSpace ℝ (Fin 3))) =
      ENNReal.ofReal (|Q.det| / D) • volume := by
  have hdetQinv : Q⁻¹.det = (Q.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv]
    simp [Ring.inverse_eq_inv']
  have hdet : LinearMap.det (Matrix.toEuclideanLin (chartMatrix D u Q)) = D * (Q.det)⁻¹ := by
    rw [det_toEuclideanLin, det_chartMatrix, hdetQinv]
  have hdet0 : LinearMap.det (Matrix.toEuclideanLin (chartMatrix D u Q)) ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hD.ne' (inv_ne_zero hQ)
  have hfun : chartAff D t₀ c u Q =
      (fun w => w + chartShift D t₀ c Q) ∘ Matrix.toEuclideanLin (chartMatrix D u Q) := by
    funext w; rw [chartAff_eq]; rfl
  have hlin : Measurable (Matrix.toEuclideanLin (chartMatrix D u Q)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  rw [hfun, ← Measure.map_map (measurable_add_const _) hlin,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet0, Measure.map_smul,
    map_add_right_eq_self, hdet]
  · congr 1
    congr 1
    rw [abs_inv, abs_mul, abs_inv, abs_of_pos hD]
    field_simp
  · exact (measurable_add_const _).aemeasurable


theorem chartMatrix_det_ne_zero {D : ℝ} (hD : 0 < D) (u : EuclideanSpace ℝ (Fin 2))
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    LinearMap.det (Matrix.toEuclideanLin (chartMatrix D u Q)) ≠ 0 := by
  have hdetQinv : Q⁻¹.det = (Q.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv]
    simp [Ring.inverse_eq_inv']
  rw [det_toEuclideanLin, det_chartMatrix, hdetQinv]
  exact mul_ne_zero hD.ne' (inv_ne_zero hQ)

/-- The chart normalization as a measurable equivalence. -/
noncomputable def chartAffEquiv (D t₀ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hD : 0 < D) (hQ : Q.det ≠ 0) :
    EuclideanSpace ℝ (Fin 3) ≃ᵐ EuclideanSpace ℝ (Fin 3) :=
  ((LinearMap.equivOfDetNeZero (Matrix.toEuclideanLin (chartMatrix D u Q))
      (chartMatrix_det_ne_zero hD u hQ)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv).trans
    (MeasurableEquiv.addRight (chartShift D t₀ c Q))

theorem chartAffEquiv_apply {D t₀ : ℝ} (c u : EuclideanSpace ℝ (Fin 2))
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hD : 0 < D) (hQ : Q.det ≠ 0)
    (w : EuclideanSpace ℝ (Fin 3)) :
    chartAffEquiv D t₀ c u Q hD hQ w = chartAff D t₀ c u Q w := by
  rw [chartAff_eq]
  rfl

theorem coe_chartAffEquiv {D t₀ : ℝ} (c u : EuclideanSpace ℝ (Fin 2))
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hD : 0 < D) (hQ : Q.det ≠ 0) :
    (chartAffEquiv D t₀ c u Q hD hQ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) =
      chartAff D t₀ c u Q :=
  funext (chartAffEquiv_apply c u hD hQ)

/-- The observation-space form of the chart normalization (hidden labels unchanged). -/
noncomputable def obsChartEquiv (D t₀ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hD : 0 < D) (hQ : Q.det ≠ 0) :
    (EuclideanSpace ℝ (Fin 3) × ℤ) ≃ᵐ (EuclideanSpace ℝ (Fin 3) × ℤ) :=
  (chartAffEquiv D t₀ c u Q hD hQ).prodCongr (MeasurableEquiv.refl ℤ)

/-- The reference measure of observations. -/
noncomputable abbrev obsRef : Measure (EuclideanSpace ℝ (Fin 3) × ℤ) :=
  (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count

theorem coe_obsChartEquiv {D t₀ : ℝ} (c u : EuclideanSpace ℝ (Fin 2))
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hD : 0 < D) (hQ : Q.det ≠ 0) :
    (obsChartEquiv D t₀ c u Q hD hQ : EuclideanSpace ℝ (Fin 3) × ℤ → _) =
      Prod.map (chartAff D t₀ c u Q) id := by
  funext o
  show (chartAffEquiv D t₀ c u Q hD hQ o.1, o.2) = (chartAff D t₀ c u Q o.1, o.2)
  rw [chartAffEquiv_apply]

theorem map_obsChartEquiv_obsRef {D t₀ : ℝ} (c u : EuclideanSpace ℝ (Fin 2))
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hD : 0 < D) (hQ : Q.det ≠ 0) :
    Measure.map (obsChartEquiv D t₀ c u Q hD hQ) obsRef =
      ENNReal.ofReal (|Q.det| / D) • obsRef := by
  have h := Measure.map_prod_map (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (Measure.count : Measure ℤ) (chartAffEquiv D t₀ c u Q hD hQ).measurable measurable_id
  rw [Measure.map_id, coe_chartAffEquiv, map_chartAff_volume hD c u hQ,
    Measure.prod_smul_left] at h
  rw [coe_obsChartEquiv, ← h]

/-- Pushing a density forward under a measurable equivalence that scales the reference
measure by a constant. -/
theorem map_equiv_withDensity {α : Type*} [MeasurableSpace α] (ρ : Measure α)
    (e : α ≃ᵐ α) (c : ℝ≥0∞) (he : Measure.map e ρ = c • ρ) {H : α → ℝ≥0∞}
    (hH : Measurable H) :
    Measure.map e (ρ.withDensity H) = ρ.withDensity (fun o => c * H (e.symm o)) := by
  ext S hS
  rw [Measure.map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    withDensity_apply _ hS]
  have h1 : (∫⁻ o in e ⁻¹' S, H o ∂ρ) = ∫⁻ o in S, H (e.symm o) ∂(Measure.map e ρ) := by
    rw [Measure.restrict_map e.measurable hS, lintegral_map_equiv]
    simp
  rw [h1, he, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  exact (lintegral_const_mul c (hH.comp e.symm.measurable)).symm

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp
