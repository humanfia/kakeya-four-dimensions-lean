import Submission.Obl.k4_horizontal_strict_parameter_step.AffineUpgrade
import Submission.Obl.k4_horizontal_strict_parameter_step.NormalizedResidual

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ChartCoordinates.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- Static parameters and affine scalar coefficients in one old full-time chart.
Outside the chart assignment the coordinates are set to zero, so their bounds are
pointwise on the original trajectory type, as required by the first-jet input. -/
def chartCoordinates {α : Type*} (A : Set α) (b : α → Fin 6 → ℝ)
    (h : Fin 6 → ℝ) (a D p₀ q₀ : ℝ) : α → Fin 4 → ℝ := by
  classical
  exact A.piecewise (fun l => ![(b l 0 - p₀) / D, (b l 1 - q₀) / D,
    normalizedAffine h a (b l 2) (b l 5) (b l 0) (b l 1) 0,
    normalizedAffine h a (b l 2) (b l 5) (b l 0) (b l 1) 1]) (fun _ => 0)

theorem measurable_chartCoordinates {α : Type*} [MeasurableSpace α] {A : Set α}
    (hA : MeasurableSet A) {b : α → Fin 6 → ℝ} (hb : Measurable b)
    (h : Fin 6 → ℝ) (a D p₀ q₀ : ℝ) :
    Measurable (chartCoordinates A b h a D p₀ q₀) := by
  classical
  unfold chartCoordinates
  apply Measurable.piecewise hA
  · unfold normalizedAffine
    fun_prop
  · exact measurable_const

/-- The old full-time fit bounds the normalized coefficients and the old static
square bounds the normalized tangential coordinates. -/
theorem chartCoordinates_bounds {α : Type*} {A : Set α} {b : α → Fin 6 → ℝ}
    {h : Fin 6 → ℝ} {a D p₀ q₀ M : ℝ} (ha : 0 < a) (hD : 0 < D) (hM : 0 ≤ M)
    (hbox : ∀ l ∈ A, b l 0 ∈ Icc p₀ (p₀ + D) ∧ b l 1 ∈ Icc q₀ (q₀ + D))
    (hfit : ∀ l ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
      |b l 2 + t * b l 5 - predictor h t (b l 0) (b l 1)| ≤ M * a) :
    ∀ l, |chartCoordinates A b h a D p₀ q₀ l 0| ≤ 1 ∧
      |chartCoordinates A b h a D p₀ q₀ l 1| ≤ 1 ∧
      |chartCoordinates A b h a D p₀ q₀ l 2| ≤ M ∧
      |chartCoordinates A b h a D p₀ q₀ l 3| ≤ 2 * M := by
  classical
  intro l
  by_cases hl : l ∈ A
  · have hb := hbox l hl
    have hr := normalizedAffine_bounds ha (hfit l hl)
    have hy {x c : ℝ} (hx : x ∈ Icc c (c + D)) : |(x - c) / D| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg (by linarith [hx.1]) hD.le), div_le_one hD]
      linarith [hx.2]
    simp only [chartCoordinates, piecewise_eq_of_mem _ _ _ hl]
    change |(b l 0 - p₀) / D| ≤ 1 ∧ |(b l 1 - q₀) / D| ≤ 1 ∧
      |normalizedAffine h a (b l 2) (b l 5) (b l 0) (b l 1) 0| ≤ M ∧
      |normalizedAffine h a (b l 2) (b l 5) (b l 0) (b l 1) 1| ≤ 2 * M
    exact ⟨hy hb.1, hy hb.2, hr.2.1, hr.2.2⟩
  · simp only [chartCoordinates, piecewise_eq_of_notMem _ _ _ hl, Pi.zero_apply, abs_zero]
    exact ⟨by norm_num, by norm_num, hM, by linarith⟩

/-- The scalar represented by the chart coefficients is exactly the original
trajectory after subtracting and dividing by its full-time predictor. -/
theorem chartCoordinates_scalar {α : Type*} {A : Set α} {b : α → Fin 6 → ℝ}
    (h : Fin 6 → ℝ) {a : ℝ} (ha : a ≠ 0) (D p₀ q₀ : ℝ) {l : α} (hl : l ∈ A) (t : ℝ) :
    chartCoordinates A b h a D p₀ q₀ l 2 + t * chartCoordinates A b h a D p₀ q₀ l 3 =
      (b l 2 + t * b l 5 - predictor h t (b l 0) (b l 1)) / a := by
  classical
  simp only [chartCoordinates, piecewise_eq_of_mem _ _ _ hl]
  change normalizedAffine h a (b l 2) (b l 5) (b l 0) (b l 1) 0 +
    t * normalizedAffine h a (b l 2) (b l 5) (b l 0) (b l 1) 1 = _
  simp only [normalizedAffine, Matrix.cons_val_zero, Matrix.cons_val_one, predictor]
  ring

end

end Submission.Obl.k4_horizontal_strict_parameter_step
