/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/TriangularCoordinates.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
/- Adapted from this LOT tree, obligation o202, session x0698, commit
   af82e6f9c71df56ed963f4a992dea84d0d6d83b5, file
   Submission/Obl/k4_horizontal_subcritical_rate_candidates/TriangularCoordinates.lean.
   This generic kernel uses original finite cell caps and witness mass only. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation

namespace Submission.Obl.k4_horizontal_strict_parameter_step

/-- Coordinates sending a tilted box of radii r to the unit cube. -/
noncomputable def triangularCoordinates (t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ : ℝ)
    (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(1 + (z 0 - t₀) / r₀) / 2,
    (1 + (z 1 - z₀ - l₁ * (z 0 - t₀)) / r₁) / 2,
    (1 + (z 2 - y₀ - l₂ * (z 0 - t₀) - l₃ * (z 1 - z₀)) / r₂) / 2]


end Submission.Obl.k4_horizontal_strict_parameter_step
