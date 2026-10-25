/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at c7228243ba9237e7d6cd8a43298ef6dbf77acd93, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/ChartScalar.lean`.
Only the namespace and internal imports are changed; unused NativeComparison import removed. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.RawCharts
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.ResidualSupport

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set

namespace RawChart

/-- On a chart's actual original assignment, its first-jet scalar is precisely
the normalized physical residual with the selected native row subtracted. -/
theorem scalar_eq_original_residual {α : Type} [MeasurableSpace α]
    (C : RawChart α) (b : α → Fin 6 → ℝ) (f : Fin 6 → ℝ)
    {a D : ℝ} (ha : a ≠ 0) {l : α} (hl : l ∈ C.A) (t : ℝ)
    (hF : C.F t = normalizedRow f C.h D a t) :
    FirstJet.scal (C.y b a D) (C.β b a D) (C.γ b a D) C.F l t =
      normalizedResidual f C.h D a ((C.q 1 : ℝ) * D) ((C.q 2 : ℝ) * D)
        t (b l 0) (b l 1) (b l 2 + t * b l 5) := by
  classical
  have hx : C.β b a D l + t * C.γ b a D l =
      (b l 2 + t * b l 5 - predictor C.h t (b l 0) (b l 1)) / a := by
    simpa only [β, γ, coordinates] using
      chartCoordinates_scalar (A := C.A) (b := b) C.h ha D ((C.q 1 : ℝ) * D) ((C.q 2 : ℝ) * D) hl t
  have hy₀ : C.y b a D l 0 = (b l 0 - (C.q 1 : ℝ) * D) / D := by
    simp [y, coordinates, chartCoordinates, hl]
  have hy₁ : C.y b a D l 1 = (b l 1 - (C.q 2 : ℝ) * D) / D := by
    simp [y, coordinates, chartCoordinates, hl]
  rw [FirstJet.scal, FirstJet.xbar, hx, hy₀, hy₁, hF]
  simp only [normalizedResidual]
  ring

end RawChart
end Submission.Obl.k4_horizontal_strict_parameter_step
