/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUnitTime.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUnitTime.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real

/-! The original unit-time law, with exact product and swap identities. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

noncomputable def scalarUnitTime : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

theorem scalarUnitTime_probability : IsProbabilityMeasure scalarUnitTime :=
  ⟨by simp only [scalarUnitTime, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one]⟩

theorem scalarUnitTime_le_volume : scalarUnitTime ≤ volume := Measure.restrict_le_self

theorem original_unit_time_prod_mass {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    (ν.prod scalarUnitTime) E = (ν.prod volume) E := by
  have hprod : ν.prod scalarUnitTime =
      (ν.prod volume).restrict (univ ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [scalarUnitTime, Measure.restrict_univ] using
      (Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) univ (Icc (0 : ℝ) 1))
  rw [hprod, Measure.restrict_apply hE, inter_eq_left.mpr hunit]

theorem original_unit_time_prod_real {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    (ν.prod scalarUnitTime).real E = (ν.prod volume).real E :=
  congrArg ENNReal.toReal (original_unit_time_prod_mass ν hE hunit)

theorem original_unit_time_swap_mass {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    (scalarUnitTime.prod ν) (Prod.swap ⁻¹' E) = (ν.prod volume) E := by
  letI : IsProbabilityMeasure scalarUnitTime := scalarUnitTime_probability
  have hswap := congrArg (fun m : Measure (Λ × ℝ) => m E)
    (Measure.prod_swap (μ := scalarUnitTime) (ν := ν))
  rw [Measure.map_apply measurable_swap hE] at hswap
  exact hswap.trans (original_unit_time_prod_mass ν hE hunit)

theorem original_unit_time_swap_real {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    (scalarUnitTime.prod ν).real (Prod.swap ⁻¹' E) = (ν.prod volume).real E :=
  congrArg ENNReal.toReal (original_unit_time_swap_mass ν hE hunit)

theorem original_unit_incidence_ne_top {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) : (ν.prod volume) E ≠ ⊤ := by
  letI : IsProbabilityMeasure scalarUnitTime := scalarUnitTime_probability
  rw [← original_unit_time_swap_mass ν hE hunit]
  exact measure_ne_top _ _

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
