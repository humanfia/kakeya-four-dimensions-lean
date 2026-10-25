/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/TimeRestoration.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o202, session x0698, commit aacc14fa,
   `Submission/Obl/k4_horizontal_subcritical_rate_candidates/TimeRestoration.lean`. Original imports of accepted libraries are retained. -/
import Submission.Lib.K4TimeMarginalRestoration

/-!
A selected trajectory locates a time set; all original paired incidences at
those times are then restored. No incidence law is normalized in this step.
-/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set

/-- Restore all paired lines at the times supplied by one long trajectory witness. -/
lemma exists_restored_time_witness {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    {C m c : ℝ} (hC : 0 < C) (hm : 0 < m) (hc : 0 ≤ c)
    (hdom : ρ ≤ ENNReal.ofReal C • (ν.prod volume))
    {E : Set (α × ℝ)} {T₀ : Set ℝ} (hE : MeasurableSet E)
    (hmass : ENNReal.ofReal m ≤ ρ E) (hsub : E ⊆ univ ×ˢ T₀)
    (hrestore : ∀ T : Set ℝ, MeasurableSet T → T ⊆ T₀ →
      ENNReal.ofReal c * volume T ≤ ρ (E ∩ (univ ×ˢ T))) :
    ∃ l : α, MeasurableSet (Prod.mk l ⁻¹' E) ∧
      ENNReal.ofReal (m / (2 * C)) ≤ volume (Prod.mk l ⁻¹' E) ∧
      ENNReal.ofReal (c * m / (2 * C)) ≤ ρ (E ∩ (univ ×ˢ (Prod.mk l ⁻¹' E))) := by
  exact Submission.Lib.K4TimeMarginalRestoration.exists_restored_time_witness
    ν ρ hC hm hc hdom hE hmass hsub hrestore

end Submission.Obl.k4_subcritical_corrected_scalar_charts
