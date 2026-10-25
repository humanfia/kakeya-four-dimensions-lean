-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/MassReturn.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.ModelMeasures

namespace Submission.Obl.k4_finite_affine_candidate_return

open MeasureTheory

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The model prior continues to use the full original assignment. -/
theorem nuE_apply_subset (ν : Measure α) (A₀ A : Set α)
    (hA : MeasurableSet A) (hsub : A ⊆ A₀) :
    nuE ν A₀ A = (ν A₀)⁻¹ * ν A := by
  rw [nuE, Measure.smul_apply, Measure.restrict_apply hA,
    Set.inter_eq_left.mpr hsub, smul_eq_mul]

/-- Return a model event's relative floor to the unchanged original prior.
The normalizing parent mass cancels, and parent time is restored exactly. -/
theorem muE_floor_return (ν : Measure α) (A₀ A : Set α)
    (hA : MeasurableSet A) (hsub : A ⊆ A₀) (h0 : ν A₀ ≠ 0) (hT : ν A₀ ≠ ⊤)
    (t₀ q : ℝ) (hq : 0 < q) (S X : Set (α × ℝ)) (hX : MeasurableSet X)
    (c : ENNReal) (hfloor : c * nuE ν A₀ A ≤ muE ν A₀ t₀ q S X) :
    ENNReal.ofReal q * c * ν A ≤ (ν.prod volume) (tnorm t₀ q ⁻¹' X ∩ S) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hd0 : ENNReal.ofReal q * ν A₀ ≠ 0 := mul_ne_zero hq0 h0
  have hdT : ENNReal.ofReal q * ν A₀ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT
  have h := mul_le_mul_right hfloor (ENNReal.ofReal q * ν A₀)
  rw [nuE_apply_subset ν A₀ A hA hsub, muE_apply ν A₀ t₀ q S hX] at h
  have hl : ENNReal.ofReal q * ν A₀ * (c * ((ν A₀)⁻¹ * ν A)) =
      ENNReal.ofReal q * c * ν A := by
    calc _ = ENNReal.ofReal q * c * (ν A₀ * (ν A₀)⁻¹) * ν A := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel h0 hT, mul_one]
  have hr : ENNReal.ofReal q * ν A₀ *
      ((ENNReal.ofReal q * ν A₀)⁻¹ * (ν.prod volume) (tnorm t₀ q ⁻¹' X ∩ S)) =
      (ν.prod volume) (tnorm t₀ q ⁻¹' X ∩ S) := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hd0 hdT, one_mul]
  rwa [hl, hr] at h

/-- An inclusion on original incidences is sufficient for returning the floor. -/
theorem muE_floor_return_mono (ν : Measure α) (A₀ A : Set α)
    (hA : MeasurableSet A) (hsub : A ⊆ A₀) (h0 : ν A₀ ≠ 0) (hT : ν A₀ ≠ ⊤)
    (t₀ q : ℝ) (hq : 0 < q) (S X Y : Set (α × ℝ)) (hX : MeasurableSet X)
    (hXY : tnorm t₀ q ⁻¹' X ∩ S ⊆ Y)
    (c : ENNReal) (hfloor : c * nuE ν A₀ A ≤ muE ν A₀ t₀ q S X) :
    ENNReal.ofReal q * c * ν A ≤ (ν.prod volume) Y :=
  (muE_floor_return ν A₀ A hA hsub h0 hT t₀ q hq S X hX c hfloor).trans
    (measure_mono hXY)

end

end Submission.Obl.k4_finite_affine_candidate_return
