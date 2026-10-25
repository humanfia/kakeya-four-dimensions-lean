import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CmpAffine
import Submission.Obl.k4_finite_width_output_exclusion.Definitions
set_option autoImplicit false

/-! Exact transport of selected laws and observations under a chart normalization:
the new prior is the conditioned, coefficient-transported old prior, and the new
observation is the chart image of the old observation at the combined thickness. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp

open MeasureTheory Set
open scoped ENNReal

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Point := Line × ℝ

/-- Old-to-new time coordinate of a chart. -/
noncomputable def timeEquiv (D t₀ : ℝ) (hD : 0 < D) : ℝ ≃ᵐ ℝ where
  toFun t := (t - t₀) * D
  invFun τ := t₀ + τ / D
  left_inv t := by field_simp; ring
  right_inv τ := by field_simp; ring
  measurable_toFun := (measurable_id.sub_const _).mul_const _
  measurable_invFun := measurable_const.add (measurable_id.div_const _)

theorem map_timeEquiv_volume {D t₀ : ℝ} (hD : 0 < D) :
    Measure.map (timeEquiv D t₀ hD) volume = ENNReal.ofReal D⁻¹ • volume := by
  have : (timeEquiv D t₀ hD : ℝ → ℝ) = (fun t => t * D) ∘ (fun t => t - t₀) := rfl
  rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_sub_const _),
    map_sub_right_eq_self, Real.map_volume_mul_right hD.ne', abs_inv, abs_of_pos hD]

/-- Old-to-new incidence coordinates of a chart. -/
noncomputable def incEquiv (θ : Line ≃ᵐ Line) (D t₀ : ℝ) (hD : 0 < D) : Point ≃ᵐ Point :=
  θ.prodCongr (timeEquiv D t₀ hD)

theorem incEquiv_apply (θ : Line ≃ᵐ Line) {D t₀ : ℝ} (hD : 0 < D) (z : Point) :
    incEquiv θ D t₀ hD z = (θ z.1, (z.2 - t₀) * D) := rfl

theorem incEquiv_symm_apply (θ : Line ≃ᵐ Line) {D t₀ : ℝ} (hD : 0 < D) (z : Point) :
    (incEquiv θ D t₀ hD).symm z = (θ.symm z.1, t₀ + z.2 / D) := rfl

/-- **Exact prior transport.** The selected law of a conditioned, normalized chart
prior is `D / ν(A)` times the image of the old restricted selected law. -/
theorem selected_law_transport (ν : Measure Line) [IsFiniteMeasure ν]
    (A : Set Line) (θ : Line ≃ᵐ Line) {D t₀ : ℝ} (hD : 0 < D)
    {E : Set Point} (hE : MeasurableSet E) :
    ((((ν A)⁻¹ • Measure.map θ (ν.restrict A)).prod volume).restrict E) =
      (ENNReal.ofReal D / ν A) • Measure.map (incEquiv θ D t₀ hD)
        (((ν.restrict A).prod volume).restrict (incEquiv θ D t₀ hD ⁻¹' E)) := by
  have hmap : Measure.map (incEquiv θ D t₀ hD) ((ν.restrict A).prod volume) =
      (Measure.map θ (ν.restrict A)).prod (ENNReal.ofReal D⁻¹ • volume) := by
    rw [← map_timeEquiv_volume (t₀ := t₀) hD]
    exact (Measure.map_prod_map _ _ θ.measurable (timeEquiv D t₀ hD).measurable).symm
  rw [← Measure.restrict_map (incEquiv θ D t₀ hD).measurable hE, hmap,
    Measure.prod_smul_right, Measure.prod_smul_left, Measure.restrict_smul,
    Measure.restrict_smul, smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_right_comm, ← ENNReal.ofReal_mul hD.le, mul_inv_cancel₀ hD.ne',
    ENNReal.ofReal_one, one_mul]


open Submission.Obl.k4_finite_width_output_exclusion (x y v δ obs)

theorem measurable_obs (B a : ℝ) : Measurable (obs B a) := by
  unfold obs x
  fun_prop

theorem measurable_v : Measurable v := by
  unfold v
  fun_prop

theorem y_apply_zero (l : Line) (t : ℝ) : y l t 0 = x l t 1 := rfl
theorem y_apply_one (l : Line) (t : ℝ) : y l t 1 = x l t 2 := rfl

theorem y_eq_add_smul (l : Line) (t : ℝ) : y l t = y l 0 + t • v l := by
  ext i
  fin_cases i <;> simp [y, x, v]

/-- The new observation of a transported incidence is the chart image of the old
observation at the combined hidden thickness. -/
theorem obs_incEquiv {θ : Line ≃ᵐ Line} {D t₀ : ℝ} (hD : 0 < D)
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hy : ∀ l t, y (θ l) t =
      Matrix.toEuclideanLin Q⁻¹ (y l (t₀ + t / D) - c - (t₀ + t / D) • u))
    (hx : ∀ l t, x (θ l) t 3 = x l (t₀ + t / D) 3)
    {B ρ σ : ℝ} (hρ : ρ ≠ 0) (hσ : σ ≠ 0) (z : Point) :
    obs (B / ρ) σ (incEquiv θ D t₀ hD z) =
      Prod.map (chartAff D t₀ c u Q) id (obs B (ρ * σ) z) := by
  obtain ⟨l, t⟩ := z
  have ht : t₀ + (t - t₀) * D / D = t := by field_simp; ring
  have hyl := hy l ((t - t₀) * D)
  have hxl := hx l ((t - t₀) * D)
  rw [ht] at hyl hxl
  rw [incEquiv_apply]
  simp only [obs, Prod.map]
  refine Prod.ext ?_ ?_
  · simp only [chartAff]
    congr 1
    ext i
    fin_cases i
    · rfl
    · show x (θ l) ((t - t₀) * D) 1 = _
      rw [← y_apply_zero, hyl]
      rfl
    · show x (θ l) ((t - t₀) * D) 2 = _
      rw [← y_apply_one, hyl]
      rfl
  · simp only
    rw [hxl]
    congr 1
    field_simp

/-- The velocity of a transported trajectory. -/
theorem v_transport {θ : Line ≃ᵐ Line} {D t₀ : ℝ}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hy : ∀ l t, y (θ l) t =
      Matrix.toEuclideanLin Q⁻¹ (y l (t₀ + t / D) - c - (t₀ + t / D) • u))
    (l : Line) :
    v (θ l) = D⁻¹ • Matrix.toEuclideanLin Q⁻¹ (v l - u) := by
  have h1 := hy l 1
  have h0 := hy l 0
  rw [y_eq_add_smul (θ l) 1, one_smul] at h1
  rw [y_eq_add_smul (θ l) 0, zero_smul, add_zero] at h0
  rw [h0, y_eq_add_smul l (t₀ + 1 / D), y_eq_add_smul l (t₀ + 0 / D)] at h1
  have h2 : v (θ l) = Matrix.toEuclideanLin Q⁻¹
      (y l 0 + (t₀ + 1 / D) • v l - c - (t₀ + 1 / D) • u) -
      Matrix.toEuclideanLin Q⁻¹ (y l 0 + (t₀ + 0 / D) • v l - c - (t₀ + 0 / D) • u) := by
    rw [← h1]; abel
  rw [h2, ← map_sub, ← map_smul]
  congr 1
  simp only [zero_div, add_zero, add_smul, smul_sub]
  rw [one_div]
  abel

theorem smul_withDensity_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (r : ℝ≥0∞)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    r • μ.withDensity f = μ.withDensity (fun o => r * f o) := by
  rw [← withDensity_smul r hf]
  rfl

/-- **Exact law transport** for one chart: the new pure observation law equals
`D / ν(A)` times the chart image of the old restricted law at the combined thickness. -/
theorem obs_law_transport (ν : Measure Line) [IsFiniteMeasure ν]
    (A : Set Line) (θ : Line ≃ᵐ Line) {D t₀ : ℝ} (hD : 0 < D)
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (hy : ∀ l t, y (θ l) t =
      Matrix.toEuclideanLin Q⁻¹ (y l (t₀ + t / D) - c - (t₀ + t / D) • u))
    (hx : ∀ l t, x (θ l) t 3 = x l (t₀ + t / D) 3)
    {E : Set Point} (hE : MeasurableSet E) {B ρ σ : ℝ} (hρ : ρ ≠ 0) (hσ : σ ≠ 0) :
    Measure.map (obs (B / ρ) σ)
        ((((ν A)⁻¹ • Measure.map θ (ν.restrict A)).prod volume).restrict E) =
      (ENNReal.ofReal D / ν A) • Measure.map (obsChartEquiv D t₀ c u Q hD hQ)
        (Measure.map (obs B (ρ * σ))
          (((ν.restrict A).prod volume).restrict (incEquiv θ D t₀ hD ⁻¹' E))) := by
  rw [selected_law_transport ν A θ hD hE, Measure.map_smul _ (measurable_obs _ _).aemeasurable,
    Measure.map_map (measurable_obs _ _) (incEquiv θ D t₀ hD).measurable,
    Measure.map_map (obsChartEquiv D t₀ c u Q hD hQ).measurable (measurable_obs _ _)]
  congr 2
  funext z
  simp only [Function.comp_apply]
  rw [obs_incEquiv hD hy hx hρ hσ, coe_obsChartEquiv]

/-- **Exact density transport** for one chart. -/
theorem obs_density_transport (ν : Measure Line) [IsFiniteMeasure ν]
    (A : Set Line) (θ : Line ≃ᵐ Line) {D t₀ : ℝ} (hD : 0 < D)
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (hy : ∀ l t, y (θ l) t =
      Matrix.toEuclideanLin Q⁻¹ (y l (t₀ + t / D) - c - (t₀ + t / D) • u))
    (hx : ∀ l t, x (θ l) t 3 = x l (t₀ + t / D) 3)
    {E : Set Point} (hE : MeasurableSet E) {B ρ σ : ℝ} (hρ : ρ ≠ 0) (hσ : σ ≠ 0)
    {H : EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞} (hHm : Measurable H)
    (hH : Measure.map (obs B (ρ * σ))
      (((ν.restrict A).prod volume).restrict (incEquiv θ D t₀ hD ⁻¹' E)) =
        obsRef.withDensity H) :
    Measure.map (obs (B / ρ) σ)
        ((((ν A)⁻¹ • Measure.map θ (ν.restrict A)).prod volume).restrict E) =
      obsRef.withDensity (fun o => ENNReal.ofReal |Q.det| / ν A *
        H ((obsChartEquiv D t₀ c u Q hD hQ).symm o)) := by
  rw [obs_law_transport ν A θ hD hQ hy hx hE hρ hσ, hH,
    map_equiv_withDensity obsRef _ _ (map_obsChartEquiv_obsRef c u hD hQ) hHm,
    smul_withDensity_eq _ _ (f := fun o => ENNReal.ofReal (|Q.det| / D) *
      H ((obsChartEquiv D t₀ c u Q hD hQ).symm o))
      (measurable_const.mul (hHm.comp (MeasurableEquiv.measurable _)))]
  congr 1
  funext o
  rw [← mul_assoc]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, ← ENNReal.ofReal_mul hD.le,
    div_eq_mul_inv, mul_comm |Q.det|, ← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul]

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp
