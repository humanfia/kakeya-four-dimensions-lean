/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockMass.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockMass.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedSupport
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockTime

/-! Exact original masses for the actual centered block events. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem original_centered_event_real {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    {A : Set Λ} (hA : MeasurableSet A) (s anchor : ℝ) {H : ℝ} (hH : 0 < H)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) :
    ((scalarIntervalTime (-anchor)).prod ν).real
      (scalarCenteredEvent E A (s + H * anchor) H) =
        (ν.prod volume).real (E ∩ (A ×ˢ univ)) / H := by
  have hm := original_centered_block_real ν s anchor hH
    (hE.inter (hA.prod MeasurableSet.univ))
    (show E ∩ (A ×ˢ univ) ⊆ univ ×ˢ Icc s (s + H) from fun _ hp => hblock hp.1)
  convert hm using 1
  congr 1
  ext p
  simp only [scalarCenteredEvent, scalarCenteredLift, mem_inter_iff, mem_preimage,
    mem_prod, mem_univ, true_and, and_true, mem_setOf_eq]

theorem original_recentered_event_real {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    {A : Set Λ} (hA : MeasurableSet A) (s anchor : ℝ) {H : ℝ} (hH : 0 < H)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) :
    ((scalarIntervalTime (-anchor)).prod ν).real
      (scalarCenteredEvent E A (s + H * anchor) H) =
        (scalarUnitTime.prod ν).real (scalarCenteredEvent E A s H) := by
  rw [original_centered_event_real ν hE hA s anchor hH hblock]
  have hm := original_centered_event_real ν hE hA s 0 hH hblock
  simpa only [neg_zero, scalarIntervalTime, zero_add, scalarUnitTime, mul_zero, add_zero] using hm.symm

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
