/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

import Mathlib

namespace Submission.Obl.k4_dyadic_crop_affine_laws.Framework

open MeasureTheory Set
open scoped ENNReal

/-- Conditioning on a prior cell, followed by an invertible coordinate change. -/
noncomputable def conditionedPrior {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (A : Set X) (e : X ≃ᵐ Y) : Measure Y :=
  (ν A)⁻¹ • (ν.restrict A).map e

lemma conditionedPrior_probability {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (A : Set X) (e : X ≃ᵐ Y) (hA : ν A ≠ 0) (hAfin : ν A ≠ ∞) :
    IsProbabilityMeasure (conditionedPrior ν A e) := by
  rw [isProbabilityMeasure_iff, conditionedPrior, Measure.smul_apply,
    e.measurableEmbedding.map_apply, preimage_univ, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hA hAfin

/-- A marginal ceiling changes by the marginal Jacobian divided by the prior
cell mass. The assertion includes arbitrary sets, as does the frozen ceiling. -/
lemma conditionedPrior_marginal_bound
    {X Y S T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure X) (A : Set X) (e : X ≃ᵐ Y)
    (s : X → S) (t : Y → T) (h : S ≃ᵐ T)
    (hcomm : ∀ x, t (e x) = h (s x))
    (ξ : Measure S) (ζ : Measure T) (C J : ENNReal)
    (hceiling : ∀ Z : Set S, ν {x | s x ∈ Z} ≤ C * ξ Z)
    (hJac : ξ.map h = J • ζ) (Z : Set T) :
    conditionedPrior ν A e {y | t y ∈ Z} ≤ ((ν A)⁻¹ * C * J) * ζ Z := by
  rw [conditionedPrior, Measure.smul_apply, e.measurableEmbedding.map_apply]
  change (ν A)⁻¹ * (ν.restrict A) {x | t (e x) ∈ Z} ≤ _
  have heq : {x | t (e x) ∈ Z} = {x | s x ∈ h ⁻¹' Z} := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, hcomm]
  rw [heq]
  have hvol : ξ (h ⁻¹' Z) = J * ζ Z := by
    rw [← h.measurableEmbedding.map_apply, hJac, Measure.smul_apply, smul_eq_mul]
  calc
    (ν A)⁻¹ * (ν.restrict A) {x | s x ∈ h ⁻¹' Z} ≤
        (ν A)⁻¹ * ν {x | s x ∈ h ⁻¹' Z} :=
      mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
    _ ≤ (ν A)⁻¹ * (C * ξ (h ⁻¹' Z)) := mul_le_mul' le_rfl (hceiling _)
    _ = ((ν A)⁻¹ * C * J) * ζ Z := by rw [hvol]; ac_rfl

end Submission.Obl.k4_dyadic_crop_affine_laws.Framework
