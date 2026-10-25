import Submission.Obl.k4_native_finite_terminal_atlas_lift.ProductTransport

/-! Adapted from this LOT tree o178, session x0588, commit
da9ec572fe2b08c7e9d46801a7a5d1e9b1047e3f, `BlockLaws.lean`.
Only the time variable is changed; all denominators use full original priors. -/

namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory
open Submission.Obl.k4_native_finite_terminal_atlas_lift

noncomputable section

/-- Change only the time variable to the unit block, dividing by block length
times the full original assignment prior. -/
def unitBlockLaw (ν : Measure Trajectory) (A : Set Trajectory) (t₀ q : ℝ) (hq : 0 < q)
    (μ : Measure Incidence) : Measure Incidence :=
  (ENNReal.ofReal q * ν A)⁻¹ •
    μ.map (normalizedIncidenceEquiv (MeasurableEquiv.refl _) t₀ q hq.ne')

theorem unitBlockLaw_mass (ν : Measure Trajectory) (A : Set Trajectory) (t₀ q : ℝ)
    (hq : 0 < q) (μ : Measure Incidence) :
    unitBlockLaw ν A t₀ q hq μ Set.univ =
      (ENNReal.ofReal q * ν A)⁻¹ * μ Set.univ := by
  rw [unitBlockLaw, Measure.smul_apply,
    (normalizedIncidenceEquiv (MeasurableEquiv.refl _) t₀ q hq.ne').map_apply,
    Set.preimage_univ, smul_eq_mul]

/-- The full original budget restores the original analytical incidence law
exactly, even when that law has been restricted by arbitrary analytical masks. -/
theorem unitBlockLaw_restore (ν : Measure Trajectory) (A : Set Trajectory) (t₀ q : ℝ)
    (hq : 0 < q) (μ : Measure Incidence) (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤) :
    (ENNReal.ofReal q * ν A) •
      (unitBlockLaw ν A t₀ q hq μ).map
        (normalizedIncidenceEquiv (MeasurableEquiv.refl _) t₀ q hq.ne').symm = μ := by
  have hzero : ENNReal.ofReal q * ν A ≠ 0 :=
    mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) hA
  have hfinite : ENNReal.ofReal q * ν A ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
  rw [unitBlockLaw, Measure.map_smul _
    (normalizedIncidenceEquiv (MeasurableEquiv.refl _) t₀ q hq.ne').symm.measurable.aemeasurable,
    smul_smul, ENNReal.mul_inv_cancel hzero hfinite, one_smul,
    MeasurableEquiv.map_symm_map]

/-- Unit-block normalization is dominated by the unchanged conditional prior,
with no selected-incidence mass in its denominator. -/
theorem unitBlockLaw_le_conditional (ν : Measure Trajectory) [SFinite ν]
    (A : Set Trajectory) (t₀ q : ℝ) (hq : 0 < q) (μ : Measure Incidence)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤)
    (hμ : μ ≤ (ν.restrict A).prod volume) :
    unitBlockLaw ν A t₀ q hq μ ≤ ((ν A)⁻¹ • ν.restrict A).prod volume := by
  have hzero : ENNReal.ofReal q * ν A ≠ 0 :=
    mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) hA
  have hfinite : ENNReal.ofReal q * ν A ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
  have hmap := Measure.map_mono hμ
    (normalizedIncidenceEquiv (MeasurableEquiv.refl _) t₀ q hq.ne').measurable
  have hnorm := map_assigned_product_conditioned ν A hA hAfin
    (MeasurableEquiv.refl _) t₀ q hq
  have hid : Measure.map (MeasurableEquiv.refl Trajectory) (ν.restrict A) = ν.restrict A := by
    change Measure.map id (ν.restrict A) = ν.restrict A
    rw [Measure.map_id]
  simp only [Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior,
    hid] at hnorm
  rw [hnorm] at hmap
  intro S
  have h := mul_le_mul' (le_refl (ENNReal.ofReal q * ν A)⁻¹) (hmap S)
  simpa only [unitBlockLaw, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel hzero hfinite, one_mul] using h

/-- Original time support becomes exact unit-time support. -/
theorem unitBlockLaw_unit_time (ν : Measure Trajectory) (A : Set Trajectory) (t₀ q : ℝ)
    (hq : 0 < q) (μ : Measure Incidence)
    (htime : μ (Set.univ ×ˢ Set.Icc t₀ (t₀ + q))ᶜ = 0) :
    unitBlockLaw ν A t₀ q hq μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  let e := normalizedIncidenceEquiv (MeasurableEquiv.refl Trajectory) t₀ q hq.ne'
  have hwindow (p : Incidence) :
      e p ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ↔
        p ∈ Set.univ ×ˢ Set.Icc t₀ (t₀ + q) := by
    change (True ∧ 0 ≤ (p.2 - t₀) / q ∧ (p.2 - t₀) / q ≤ 1) ↔
      (True ∧ t₀ ≤ p.2 ∧ p.2 ≤ t₀ + q)
    rw [le_div_iff₀ hq, div_le_iff₀ hq]
    constructor <;> rintro ⟨_, h1, h2⟩ <;> refine ⟨trivial, ?_, ?_⟩ <;> linarith
  have heq : e ⁻¹' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ =
      (Set.univ ×ˢ Set.Icc t₀ (t₀ + q))ᶜ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_compl_iff, hwindow]
  change ((ENNReal.ofReal q * ν A)⁻¹ • μ.map e) _ = 0
  rw [Measure.smul_apply, e.map_apply, heq, htime, smul_zero]

end
end Submission.Obl.k4_balanced_native_packet_transport
