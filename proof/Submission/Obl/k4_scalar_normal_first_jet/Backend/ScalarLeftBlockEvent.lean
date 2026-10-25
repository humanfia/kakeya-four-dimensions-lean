/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarLeftBlockEvent.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarLeftBlockEvent.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Linarith

/-! The actual original event in left-normalized physical block coordinates. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

def scalarLeftBlockEvent {Λ : Type*} (E : Set (Λ × ℝ)) (A : Set Λ) (s H : ℝ) :
    Set (Λ × ℝ) := {q | (q.1, s + H * q.2) ∈ E ∧ q.1 ∈ A}

theorem scalarLeftBlockEvent_measurable {Λ : Type*} [MeasurableSpace Λ]
    {E : Set (Λ × ℝ)} (hE : MeasurableSet E) {A : Set Λ} (hA : MeasurableSet A) (s H : ℝ) :
    MeasurableSet (scalarLeftBlockEvent E A s H) :=
  (hE.preimage (measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd)))).inter
    (hA.preimage measurable_fst)

theorem scalarLeftBlockEvent_unit {Λ : Type*} {E : Set (Λ × ℝ)} {A : Set Λ} {s H : ℝ}
    (hH : 0 < H) (hblock : E ⊆ univ ×ˢ Icc s (s + H)) :
    scalarLeftBlockEvent E A s H ⊆ A ×ˢ Icc (0 : ℝ) 1 := by
  intro q hq
  have hh := (hblock hq.1).2
  exact ⟨hq.2, by nlinarith [hh.1], by nlinarith [hh.2]⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
