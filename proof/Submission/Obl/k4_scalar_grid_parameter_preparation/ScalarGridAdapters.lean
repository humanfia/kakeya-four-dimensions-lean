/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarGridAdapters.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.PhysicalSupportCover

/-! Read the frozen vector-valued pure caps as physical three-coordinate caps. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MeasureTheory
open scoped ENNReal

theorem pure_vector_grid_cap_physical {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T Y X : Ω → ℝ) (ξ : ℝ) (C : ℝ≥0∞)
    (hcap : ∀ (q : Fin 2 → ℤ) (b : ℤ),
      μ {p | (fun e : Fin 2 => (⌊(![T p,Y p] : Fin 2 → ℝ) e / ξ⌋ : ℤ)) = q ∧
        (⌊X p / ξ⌋ : ℤ) = b} ≤ C) :
    ∀ q : Fin 3 → ℤ, μ {p | physicalScalarGridTag ξ ![T p,Y p,X p] = q} ≤ C := by
  intro q
  apply le_trans (measure_mono ?_) (hcap ![q 0,q 1] (q 2))
  intro p hp
  refine ⟨?_,?_⟩
  · ext e
    fin_cases e
    · simpa [physicalScalarGridTag] using congrFun hp 0
    · simpa [physicalScalarGridTag] using congrFun hp 1
  · simpa [physicalScalarGridTag] using congrFun hp 2

end Submission.Obl.k4_scalar_grid_parameter_preparation
