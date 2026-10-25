import Submission.Obl.k4_scalar_grid_polynomial_qualification.ParameterRefinement
import Submission.Lib.K4ScalarActualSwitching.GridPalette

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory
open Submission.Lib.K4ReferencePruning

noncomputable section

def residualStateKeep {X Q : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (state : X → Q) (η : ENNReal) : Set X :=
  referenceKeep μ state (fun q => ν (state ⁻¹' {q})) η

theorem measurableSet_residualStateKeep {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ ν : Measure X) (state : X → Q) (hstate : Measurable state) (η : ENNReal) :
    MeasurableSet (residualStateKeep μ ν state η) :=
  measurableSet_referenceKeep μ state hstate _ η

/-- Renewal is paid against the original state masses, summed before any
world is selected or normalized. -/
theorem residual_state_mass_budget {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ ν : Measure X) (state : X → Q) (hstate : Measurable state) (η : ENNReal) :
    μ univ ≤ (μ.restrict (residualStateKeep μ ν state η)) univ + η * ν univ := by
  have hsum : ∑' q, ν (state ⁻¹' {q}) = ν univ := by
    simpa only [univ_inter] using
      (Submission.Obl.k4_crop_angular_finite_tail.measure_eq_tsum_label ν hstate MeasurableSet.univ).symm
  simpa only [residualStateKeep, hsum] using reference_pruning_mass_budget μ state hstate
    (fun q => ν (state ⁻¹' {q})) η

/-- A substantial residual regains the original palette ceiling after
discarding light states. The same retained-state set works at every
velocity reading because its definition does not use that reading. -/
theorem renewed_palette_cap {X Q V : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ ν : Measure X) (hμν : μ ≤ ν)
    (state : X → Q) (hstate : Measurable state)
    (code : X → V) (hcode : Measurable code) (π : Measure V) (C η : ENNReal)
    (hη0 : η ≠ 0) (hηtop : η ≠ ⊤)
    (hatom : ∀ q v, ν {p | state p = q ∧ code p = v} ≤
      C * ν (state ⁻¹' {q}) * π {v}) :
    ∀ q (A : Set V), MeasurableSet A →
      (μ.restrict (residualStateKeep μ ν state η)) {p | state p = q ∧ code p ∈ A} ≤
        (C / η) * (μ.restrict (residualStateKeep μ ν state η)) (state ⁻¹' {q}) * π A := by
  have hcap := Submission.Lib.K4ScalarActualSwitching.rectangular_palette_caps_of_atoms
    ν state hstate code hcode π C hatom
  exact reference_pruned_palette_cap μ state hstate code π
    (fun q => ν (state ⁻¹' {q})) C η hη0 hηtop
    (fun q A hA => (hμν _).trans (hcap q A hA))

/-- Keeping whole states preserves a relative palette ceiling with its
current state denominator. -/
theorem whole_state_palette_cap {X Q V : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace V]
    (μ : Measure X) (state : X → Q) (hstate : Measurable state)
    (code : X → V) (π : Measure V) (C : ENNReal) (S : Set Q)
    (hcap : ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ code p ∈ A} ≤ C * μ (state ⁻¹' {q}) * π A) :
    ∀ q (A : Set V), MeasurableSet A →
      (μ.restrict (state ⁻¹' S)) {p | state p = q ∧ code p ∈ A} ≤
        C * (μ.restrict (state ⁻¹' S)) (state ⁻¹' {q}) * π A := by
  classical
  intro q A hA
  have hmass : (μ.restrict (state ⁻¹' S)) (state ⁻¹' {q}) =
      if q ∈ S then μ (state ⁻¹' {q}) else 0 := by
    rw [Measure.restrict_apply (hstate (measurableSet_singleton q))]
    split_ifs with hq
    · congr 1
      apply inter_eq_left.mpr
      intro p hp
      simpa only [mem_preimage, mem_singleton_iff.mp hp] using hq
    · have hd : Disjoint (state ⁻¹' {q}) (state ⁻¹' S) := by
        apply disjoint_left.mpr
        intro p hp hps
        exact hq (by simpa only [mem_preimage, mem_singleton_iff.mp hp] using hps)
      rw [hd.inter_eq, measure_empty]
  by_cases hq : q ∈ S
  · rw [hmass, ite_eq_left hq]
    have hdom : μ.restrict (state ⁻¹' S) ≤ μ := Measure.restrict_le_self
    exact (hdom _).trans (hcap q A hA)
  · rw [hmass, ite_eq_right hq, mul_zero, zero_mul]
    calc
      _ ≤ (μ.restrict (state ⁻¹' S)) (state ⁻¹' {q}) := measure_mono (fun p hp => hp.1)
      _ = 0 := by rw [hmass, ite_eq_right hq]

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification
