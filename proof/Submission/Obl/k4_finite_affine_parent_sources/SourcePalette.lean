-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.ReferencePalette
import Submission.Obl.k4_finite_affine_parent_sources.PaletteNumerics

namespace Submission.Obl.k4_finite_affine_parent_sources.ReferencePalette

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The fixed original-reference palette satisfies the precise native
Frostman ceiling after the finite angular depth-menu error is paid. -/
theorem frostman_cap {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ι) (hU : Measurable U)
    (V : Ω → ℝ) (center : ι → ℝ)
    {N A unit L S v r mesh K δ : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hδ : 0 < δ) (hwidth : 2 * δ ≤ (N ^ (unit * L)) ^ (-v))
    (hclose : ∀ᵐ x ∂μ, |V x - center (U x)| ≤ δ)
    (hdepth : unit * L * v - mesh ≤ r)
    (hbudget : 6 * A * N ^ (S * mesh) ≤ K)
    (hcap : ∀ j : ℤ, μ {x | ⌊V x / ((N ^ (unit * L)) ^ (-v))⌋ = j} ≤
      ENNReal.ofReal (A * N ^ (-S * r))) (e : ℤ) :
    law μ U center δ {w | ⌊w / ((N ^ (unit * L)) ^ (-v))⌋ = e} ≤
      ENNReal.ofReal (K * (N ^ (unit * L)) ^ (-S * v)) := by
  calc
    _ ≤ 6 * ENNReal.ofReal (A * N ^ (-S * r)) :=
      bin_cap μ U hU V center hδ hwidth hclose _ hcap e
    _ = ENNReal.ofReal (6 * (A * N ^ (-S * r))) := by
      rw [show (6 : ℝ≥0∞) = ENNReal.ofReal (6 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (palette_depth_loss hN hA hS hdepth hbudget)

end
end Submission.Obl.k4_finite_affine_parent_sources.ReferencePalette
