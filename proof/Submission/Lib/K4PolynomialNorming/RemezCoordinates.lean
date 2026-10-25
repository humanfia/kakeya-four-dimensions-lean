/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

open Set MeasureTheory

namespace Submission.Lib.K4PolynomialNorming

/-- Reverse Cartesian coordinates, matching the nesting order of polynomial
coefficients. -/
noncomputable def reversePairCoordinates : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).trans MeasurableEquiv.prodComm

theorem reversePairCoordinates_apply (x : Fin 2 → ℝ) : reversePairCoordinates x = (x 1, x 0) := rfl

theorem reversePairCoordinates_symm_apply (x y : ℝ) : reversePairCoordinates.symm (x, y) = ![y, x] := by
  apply reversePairCoordinates.injective
  rw [reversePairCoordinates.apply_symm_apply, reversePairCoordinates_apply]
  rfl

theorem reversePairCoordinates_measurePreserving : MeasurePreserving reversePairCoordinates := by
  exact Measure.measurePreserving_swap.comp (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))

/-- Split off the first coordinate, reverse the remaining pair, and put the
first coordinate last. Each operation preserves product volume. -/
noncomputable def reverseTripleCoordinates : (Fin 3 → ℝ) ≃ᵐ ((ℝ × ℝ) × ℝ) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr reversePairCoordinates)).trans MeasurableEquiv.prodComm

theorem reverseTripleCoordinates_apply (x : Fin 3 → ℝ) : reverseTripleCoordinates x = ((x 2, x 1), x 0) := rfl

theorem reverseTripleCoordinates_symm_apply (x y z : ℝ) :
    reverseTripleCoordinates.symm ((x, y), z) = ![z, y, x] := by
  apply reverseTripleCoordinates.injective
  rw [reverseTripleCoordinates.apply_symm_apply, reverseTripleCoordinates_apply]
  rfl

theorem reverseTripleCoordinates_measurePreserving : MeasurePreserving reverseTripleCoordinates := by
  exact Measure.measurePreserving_swap.comp
    (((MeasurePreserving.id (volume : Measure ℝ)).prod reversePairCoordinates_measurePreserving).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0))

end Submission.Lib.K4PolynomialNorming
