/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/ScalarCellContact.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o218, session x0760, commit 1cac570d6b7e29a2b2bcfee7642734d13baeb474,
   `Submission/Obl/k4_horizontal_endpoint_wide_return/ScalarCellContact.lean`. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ScalarCellGeometry

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set

/-- The scalar parameter cell supplies the contact geometry for the WHOLE
native witness count, using the native block midpoint as the plane slope. -/
theorem scalar_parameter_native_contact (b : Fin 6 → ℝ)
    {D h σ p₀ q₀ v R τ t χ Δ : ℝ} (hD : 0 < D) (hh : 0 < h)
    (hσh : σ ≤ h) (hDh : 3 * D ≤ h) (hχD : χ ≤ D) (hnoise : Δ + χ ≤ D * h)
    (ht : t ∈ Icc (0 : ℝ) 1) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (htblock : |t - τ| ≤ h) (hp : |b 0 - p₀| ≤ D)
    (hv : |b 3 - v| ≤ χ) (hdefect : |b 4 + b 0| ≤ Δ)
    (hR : |(b 1 - q₀) / D - 2 * t * ((b 0 - p₀) / D) - R| ≤ σ) :
    |b 0 + t * b 3 - (p₀ + t * v)| ≤ h ∧
      |b 1 + t * b 4 - (q₀ + D * R - t * p₀) -
        τ * (b 0 + t * b 3 - (p₀ + t * v))| ≤ h ^ 2 := by
  obtain ⟨hZ, hY⟩ := scalar_parameter_cell_box b hD ht hτ htblock hp hv hdefect (hR.trans hσh)
  constructor
  · exact hZ.trans (by linarith)
  · have hY' : |b 1 + t * b 4 - (q₀ + D * R - t * p₀) -
        τ * (b 0 + t * b 3 - (p₀ + t * v))| ≤ D * h + h * D + Δ + χ := by
      convert hY using 1 <;> congr 1 <;> ring
    exact hY'.trans (by nlinarith)

end Submission.Obl.k4_subcritical_corrected_scalar_charts
