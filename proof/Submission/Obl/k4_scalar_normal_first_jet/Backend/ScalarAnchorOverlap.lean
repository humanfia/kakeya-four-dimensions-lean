/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarAnchorOverlap.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarAnchorOverlap.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAnchor

/-! The anchor overlap is an actual original product event, with no change of law. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem original_duration_subset_mass {Θ Λ : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ]
    (μ : Measure Θ) [IsFiniteMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {A : Set Λ} (hA : MeasurableSet A) :
    (∫ l, A.indicator (fun l => μ.real ((fun θ => (θ, l)) ⁻¹' E)) l ∂ν) =
      (μ.prod ν).real (E ∩ (univ ×ˢ A)) := by
  rw [integral_indicator hA]
  have hprod : μ.prod (ν.restrict A) = (μ.prod ν).restrict (univ ×ˢ A) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := μ) (ν := ν) univ A)
  have h : (∫ l, μ.real ((fun θ => (θ, l)) ⁻¹' E) ∂ν.restrict A) =
      (μ.prod (ν.restrict A)).real E := by
    unfold Measure.real
    rw [integral_toReal (measurable_measure_prodMk_right hE).aemeasurable
      (Filter.Eventually.of_forall fun l => measure_lt_top μ _), Measure.prod_apply_symm hE]
  rw [h, hprod, Measure.real, Measure.restrict_apply hE]
  rfl

theorem exists_original_anchor_event {Θ Λ : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {Z : Set Θ} (hZ : μ Z = 0) :
    ∃ θ ∉ Z, ((μ.prod ν).real E) ^ 2 ≤ ν.real univ *
      (μ.prod ν).real (E ∩ (univ ×ˢ (Prod.mk θ ⁻¹' E))) := by
  obtain ⟨θ, hθ, hmass⟩ := exists_original_anchor_finite μ ν hE hZ
  refine ⟨θ, hθ, ?_⟩
  rw [original_duration_subset_mass μ ν hE (measurable_prodMk_left hE)] at hmass
  exact hmass

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
