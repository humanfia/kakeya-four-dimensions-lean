import Mathlib

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory

/-- Invert the positive real lower-density coefficient without changing the original law. -/
theorem density_le_of_inv_smul_le {Ω : Type*} [MeasurableSpace Ω]
    {H : ℝ} (hH : 0 < H) (μ ν : Measure Ω)
    (h : ENNReal.ofReal H⁻¹ • μ ≤ ν) : μ ≤ ENNReal.ofReal H • ν := by
  have hne : ENNReal.ofReal H ≠ 0 := (ENNReal.ofReal_pos.mpr hH).ne'
  intro S
  have hS := h S
  simp only [Measure.smul_apply, smul_eq_mul] at hS ⊢
  calc
    _ = ENNReal.ofReal H * (ENNReal.ofReal H⁻¹ * μ S) := by
      rw [ENNReal.ofReal_inv_of_pos hH, ← mul_assoc,
        ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hS

/-- Restricting both sides to any original sub-event preserves its density constant. -/
theorem density_bound_on_subset {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (C : ENNReal) {E E₀ : Set Ω} (hsub : E ⊆ E₀)
    (h : μ.restrict E₀ ≤ C • ν.restrict E₀) : μ.restrict E ≤ C • ν.restrict E := by
  have hr := Measure.restrict_mono_measure h E
  simpa only [Measure.restrict_smul, Measure.restrict_restrict_of_subset hsub] using hr

/-- The frozen preparation's two-sided density applies to the graph's original sub-event. -/
theorem original_two_sided_density {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) {H : ℝ} (hH : 0 < H) {E E₀ : Set Ω} (hsub : E ⊆ E₀)
    (hlo : ENNReal.ofReal H⁻¹ • ν.restrict E₀ ≤ μ.restrict E₀)
    (hhi : μ.restrict E₀ ≤ ENNReal.ofReal H • ν.restrict E₀) :
    ν.restrict E ≤ ENNReal.ofReal H • μ.restrict E ∧
      μ.restrict E ≤ ENNReal.ofReal H • ν.restrict E :=
  ⟨density_bound_on_subset ν μ _ hsub (density_le_of_inv_smul_le hH _ _ hlo),
    density_bound_on_subset μ ν _ hsub hhi⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
