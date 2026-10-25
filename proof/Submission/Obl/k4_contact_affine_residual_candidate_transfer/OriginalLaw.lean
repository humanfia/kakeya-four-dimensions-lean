import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set

/-- A final incidence floor automatically gives a floor for the refined full
trajectory assignment, with the original assignment still in the reference.
This applies to arbitrary trajectory spaces and overlapping depth histories. -/
theorem incidence_floor_implies_prior_floor {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (A S : Set α) (E : Set (α × ℝ))
    {K q θ t₀ : ℝ} (hq : 0 < q) (hθ : 0 ≤ θ)
    (hdom : μ ≤ ENNReal.ofReal K • ν.prod volume)
    (hE : E ⊆ S ×ˢ Icc t₀ (t₀ + q))
    (hfloor : ENNReal.ofReal (θ * q) * ν A ≤ μ E) :
    ENNReal.ofReal θ * ν A ≤ ENNReal.ofReal K * ν S := by
  have hupper : μ E ≤ (ENNReal.ofReal K * ν S) * ENNReal.ofReal q := by
    calc
      _ ≤ (ENNReal.ofReal K • ν.prod volume) E := hdom E
      _ = ENNReal.ofReal K * (ν.prod volume) E := by
        rw [Measure.smul_apply, smul_eq_mul]
      _ ≤ ENNReal.ofReal K * (ν.prod volume) (S ×ˢ Icc t₀ (t₀ + q)) :=
        mul_le_mul_right (measure_mono hE) _
      _ = _ := by
        rw [Measure.prod_prod, Real.volume_Icc, add_sub_cancel_left]
        exact (mul_assoc _ _ _).symm
  have hh : (ENNReal.ofReal θ * ν A) * ENNReal.ofReal q ≤
      (ENNReal.ofReal K * ν S) * ENNReal.ofReal q := by
    calc
      _ = ENNReal.ofReal (θ * q) * ν A := by
        rw [ENNReal.ofReal_mul hθ]
        ac_rfl
      _ ≤ μ E := hfloor
      _ ≤ _ := hupper
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hq).ne'
    ENNReal.ofReal_ne_top).mp hh

/-- Selecting a whole ancestor preserves every descendant event floor.
The selected ancestor is a source event, not a renormalization of its mass. -/
theorem restrict_ancestor_preserves_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G A E : Set Ω) (hE : MeasurableSet E) (hEA : E ⊆ A) :
    (μ.restrict (G ∩ A)) E = (μ.restrict G) E := by
  rw [Measure.restrict_apply hE, Measure.restrict_apply hE]
  congr 1
  ext p
  constructor
  · exact fun hp => ⟨hp.1, hp.2.1⟩
  · exact fun hp => ⟨hp.1, hp.2, hEA hp.1⟩

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
