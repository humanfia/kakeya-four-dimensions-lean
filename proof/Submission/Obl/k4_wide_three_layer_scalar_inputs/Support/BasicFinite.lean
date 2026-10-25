import Submission.Obl.k4_wide_three_layer_scalar_inputs.Model
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.OriginalMarking

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original unit-time support makes the ambient incidence law finite. -/
theorem incidence_finite_of_valid (hv : cfg.Valid) (k : ℕ) : IsFiniteMeasure (cfg.μ k) := by
  obtain ⟨-, hν, -, hdom, -, hsupp, -⟩ := hv.basic k
  letI : IsProbabilityMeasure (cfg.ν k) := hν
  have hbound := Submission.Obl.k4_scalar_marked_coefficient_smoothing.original_time_support
    (cfg.ν k) (cfg.μ k) hdom hsupp
  exact ⟨hbound.2.trans_lt ENNReal.ofReal_lt_top⟩

/-- Every later law under the original incidence law is finite as well. -/
theorem retained_finite_of_valid (hv : cfg.Valid) {k : ℕ}
    (lam : Measure (α × ℝ)) (hle : lam ≤ cfg.μ k) : IsFiniteMeasure lam := by
  letI := incidence_finite_of_valid hv k
  exact isFiniteMeasure_of_le (cfg.μ k) hle

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
