/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarSlopeDuration.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarSlopeDuration.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_initial_horizon_bound.Duration
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNearSlopeCells

/-! Original incidence concentration controls the prior of long trajectories. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_initial_horizon_bound

theorem original_prior_cap_of_duration {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {A : Set Λ} (hA : MeasurableSet A)
    {τ η : ℝ} (hτ : 0 < τ)
    (hlong : ∀ l ∈ A, ENNReal.ofReal τ ≤ volume (Prod.mk l ⁻¹' E))
    (hcap : (ν.prod volume).real (E ∩ (A ×ˢ univ)) ≤ η) :
    ν.real A ≤ η / τ := by
  letI : IsFiniteMeasure (ν.withDensity (incidenceDuration E)) := finite_duration_law ν hE hunit
  have hprior : ENNReal.ofReal τ * ν A ≤ (ν.withDensity (incidenceDuration E)) A := by
    simpa only [Measure.restrict_univ] using retained_duration_prior_bound ν hE hA
      MeasurableSet.univ (ENNReal.ofReal τ) (fun l hl => hlong l hl.1)
  have hreal := ENNReal.toReal_mono (measure_ne_top (ν.withDensity (incidenceDuration E)) A) hprior
  have hcap' : (ν.withDensity (incidenceDuration E)).real A ≤ η := by
    unfold Measure.real
    rw [duration_withDensity_apply ν hE hA]
    exact hcap
  have hprod : ν.real A * τ ≤ η := by
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hτ.le] at hreal
    have hreal' : ν.real A * τ ≤ (ν.withDensity (incidenceDuration E)).real A := by
      simpa only [Measure.real, mul_comm] using hreal
    exact hreal'.trans hcap'
  exact (le_div_iff₀ hτ).mpr hprod

/-- Close-slope output mass is bounded using the ORIGINAL incidence law,
long-label floors and original cell floors, all under the same prior. -/
theorem original_near_slope_output_cap_of_incidence {Λ ι : Type*}
    [MeasurableSpace Λ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure Λ) [IsFiniteMeasure ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {A : Set Λ} (hA : MeasurableSet A)
    {code : Λ → ι} (hcode : Measurable code) (K : Finset ι)
    {slope : Λ → ℝ} (hslope : Measurable slope)
    {c Δ D m τ η C : ℝ} (hm : 0 < m) (hτ : 0 < τ) (hC : 0 ≤ C)
    (hlong : ∀ l ∈ A, ENNReal.ofReal τ ≤ volume (Prod.mk l ⁻¹' E))
    (hfloor : ∀ b ∈ K, (A ∩ code ⁻¹' {b}).Nonempty → m ≤ ν.real (A ∩ code ⁻¹' {b}))
    (hspread : ∀ l ∈ A, ∀ l' ∈ A, code l = code l' → |slope l - slope l'| ≤ D)
    (hcap : (ν.prod volume).real
      (E ∩ ({l | l ∈ A ∧ |slope l - c| ≤ Δ + D} ×ˢ univ)) ≤ η)
    (Z : Set Λ) (hZ : ∀ l ∈ Z, l ∈ A ∧ code l ∈ K ∧ |slope l - c| ≤ Δ)
    (hout : ∀ b ∈ K, ν.real (Z ∩ code ⁻¹' {b}) ≤ C) :
    ν.real Z ≤ (η / τ) / m * C := by
  have hS : MeasurableSet {l | l ∈ A ∧ |slope l - c| ≤ Δ + D} :=
    hA.inter (measurableSet_le (hslope.sub_const c).abs measurable_const)
  have hprior : ν.real {l | l ∈ A ∧ |slope l - c| ≤ Δ + D} ≤ η / τ :=
    original_prior_cap_of_duration ν hE hunit hS hτ (fun l hl => hlong l hl.1) hcap
  exact original_near_slope_output_cap ν hA hcode K slope hm hC hfloor hspread hprior Z hZ hout

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
