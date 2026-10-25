-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Kernels.StateResampling; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Adapted from this LOT tree: obligation o247 (k4_wide_common_field_velocity_lists), branch x0870, commit e81b750b34aa9824cd7568c0d87d020832257f81, file Submission/Obl/k4_wide_common_field_velocity_lists/StateResampling.lean (session x0870's work). -/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Sum

namespace Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Two independent original incidences conditional on their unchanged
finite state. The sole denominator is the original mass of that state. -/
def statePair {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (μ : Measure Ω) (state : Ω → Q) : Measure (Ω × Ω) :=
  ∑ q, (μ (state ⁻¹' {q}))⁻¹ •
    (μ.restrict (state ⁻¹' {q})).prod (μ.restrict (state ⁻¹' {q}))

/-- Finite measurable states partition the entire original measure. -/
theorem sum_state_restrict {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (μ : Measure Ω) (state : Ω → Q)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) :
    ∑ q, μ.restrict (state ⁻¹' {q}) = μ := by
  classical
  ext E hE
  simp only [Measure.finsetSum_apply, Measure.restrict_apply hE]
  have h := sum_measure_preimage_singleton (μ := μ.restrict E)
    (Finset.univ : Finset Q) (fun q _ => hs q)
  simp only [Finset.coe_univ, preimage_univ, Measure.restrict_apply_univ] at h
  simpa only [Measure.restrict_apply (hs _), inter_comm] using h

/-- A conditional redraw has exactly the original first marginal,
including the states of zero mass. -/
theorem statePair_fst {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) :
    (statePair μ state).map Prod.fst = μ := by
  rw [statePair, Measure.map_finset_sum' measurable_fst.aemeasurable]
  calc
    _ = ∑ q, μ.restrict (state ⁻¹' {q}) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_fst_prod, Measure.restrict_apply_univ,
        smul_smul]
      by_cases hzero : μ (state ⁻¹' {q}) = 0
      · simp [hzero, Measure.restrict_eq_zero.mpr hzero]
      · rw [ENNReal.inv_mul_cancel hzero (measure_ne_top μ _), one_smul]
    _ = μ := sum_state_restrict μ state hs

theorem statePair_finite {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) :
    IsFiniteMeasure (statePair μ state) := by
  apply (Measure.isFiniteMeasure_map_iff measurable_fst.aemeasurable).mp
  rw [statePair_fst μ state hs]
  infer_instance

/-- On a source event within one state the conditional pair law has its
literal product formula, with the original state denominator. -/
theorem statePair_fiber_rectangle {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) (q : Q)
    (E V : Set Ω) (hE : MeasurableSet E) (hV : MeasurableSet V)
    (hsub : E ⊆ state ⁻¹' {q}) :
    statePair μ state (E ×ˢ V) =
      (μ (state ⁻¹' {q}))⁻¹ * (μ E * μ (V ∩ state ⁻¹' {q})) := by
  classical
  simp only [statePair, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.prod_prod, Measure.restrict_apply hE, Measure.restrict_apply hV]
  rw [Finset.sum_eq_single q]
  · rw [inter_eq_left.mpr hsub]
  · intro q' _ hne
    have hempty : E ∩ state ⁻¹' {q'} = ∅ := by
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
        iff_false, not_and]
      intro hp hp'
      exact hne (hp'.symm.trans (hsub hp))
    rw [hempty, measure_empty, zero_mul, mul_zero]
  · simp

theorem statePair_fiber_rectangle_real {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) (q : Q)
    (E V : Set Ω) (hE : MeasurableSet E) (hV : MeasurableSet V)
    (hsub : E ⊆ state ⁻¹' {q}) :
    (statePair μ state).real (E ×ˢ V) =
      μ.real E * μ.real (V ∩ state ⁻¹' {q}) / μ.real (state ⁻¹' {q}) := by
  rw [Measure.real, statePair_fiber_rectangle μ state hs q E V hE hV hsub]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, Measure.real, div_eq_mul_inv]
  ring

/-- The probability of any target event is bounded conditionally on
the source by its original statewise palette ceiling. -/
theorem statePair_rectangle_cap {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q}))
    (C : ℝ≥0∞) (E V : Set Ω) (hE : MeasurableSet E) (hV : MeasurableSet V)
    (hcap : ∀ q, μ (V ∩ state ⁻¹' {q}) ≤ C * μ (state ⁻¹' {q})) :
    statePair μ state (E ×ˢ V) ≤ C * μ E := by
  have hsum : (∑ q, μ (E ∩ state ⁻¹' {q})) = μ E := by
    have h := congrArg (fun ν : Measure Ω => ν E) (sum_state_restrict μ state hs)
    simpa only [Measure.finsetSum_apply, Measure.restrict_apply hE] using h
  calc
    _ = ∑ q, (μ (state ⁻¹' {q}))⁻¹ *
        (μ (E ∩ state ⁻¹' {q}) * μ (V ∩ state ⁻¹' {q})) := by
      simp only [statePair, Measure.finsetSum_apply, Measure.smul_apply,
        smul_eq_mul, Measure.prod_prod, Measure.restrict_apply hE,
        Measure.restrict_apply hV]
    _ ≤ ∑ q, C * μ (E ∩ state ⁻¹' {q}) := by
      apply Finset.sum_le_sum
      intro q _
      by_cases hzero : μ (state ⁻¹' {q}) = 0
      · have hz : μ (E ∩ state ⁻¹' {q}) = 0 :=
          measure_mono_null inter_subset_right hzero
        simp [hzero, hz]
      · calc
          _ ≤ (μ (state ⁻¹' {q}))⁻¹ *
              (μ (E ∩ state ⁻¹' {q}) * (C * μ (state ⁻¹' {q}))) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (hcap q))
          _ = C * μ (E ∩ state ⁻¹' {q}) := by
            calc
              _ = (C * μ (E ∩ state ⁻¹' {q})) *
                  ((μ (state ⁻¹' {q}))⁻¹ * μ (state ⁻¹' {q})) := by ring
              _ = _ := by rw [ENNReal.inv_mul_cancel hzero (measure_ne_top μ _), mul_one]
    _ = _ := by rw [← Finset.mul_sum, hsum]

end

end Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels
