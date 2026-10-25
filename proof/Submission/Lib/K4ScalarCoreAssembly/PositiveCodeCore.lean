/-
Adapted from: here:o062
Original proof: o062/x0212, 71f65b82, Submission/Obl/k4_scalar_mesh_projection/PositiveCodeCore.lean.
Original law, observed physical palettes and witness rows remain unnormalized.
-/

import Mathlib
import Submission.Lib.K4ScalarCoreAssembly.Support

namespace Submission.Lib.K4ScalarCoreAssembly

open Submission.Lib.K4ScalarCoreTools.Finalization
open Submission.Lib.K4ScalarCoreTools.Simulation.Switching
open Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching.Switching

open Set MeasureTheory

theorem ae_original_code_fiber_nonzero {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (code : Ω → I) :
    ∀ᵐ ω ∂μ, μ {ω' | code ω'=code ω} ≠ 0 := by
  have hcode (i : I) : ∀ᵐ ω ∂μ, code ω=i → μ {ω' | code ω'=i} ≠ 0 := by
    by_cases hi : μ {ω' | code ω'=i}=0
    · apply ae_iff.mpr
      apply measure_mono_null _ hi
      intro ω hω
      change ¬(code ω=i → μ {ω' | code ω'=i} ≠ 0) at hω
      change code ω=i
      by_contra hne
      exact hω (fun h => (hne h).elim)
    · exact Filter.Eventually.of_forall fun _ _ => hi
  filter_upwards [ae_all_iff.mpr hcode] with ω hω
  exact hω (code ω) rfl

/-- Removing null countable code classes leaves exactly the same
restricted original law and gives pointwise positive-class witnesses. -/
theorem exists_original_positive_code_core {Ω I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
    (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (code : Ω → I) (hcode : Measurable code) :
    ∃ U : Set Ω, MeasurableSet U ∧ U ⊆ A ∧ μ.restrict U=μ.restrict A ∧
      ∀ ω ∈ U, μ (A ∩ {ω' | code ω'=code ω}) ≠ 0 := by
  let Good : Set I := {i | (μ.restrict A) {ω | code ω=i} ≠ 0}
  have hGood : MeasurableSet Good := (Set.to_countable Good).measurableSet
  let B := code ⁻¹' Good
  have hB : MeasurableSet B := hGood.preimage hcode
  have hae : ∀ᵐ ω ∂μ.restrict A, ω ∈ B := ae_original_code_fiber_nonzero (μ.restrict A) code
  let U := A ∩ B
  have hμ : μ.restrict U=μ.restrict A := by
    rw [show U=B ∩ A by exact inter_comm A B,← Measure.restrict_restrict hB]
    exact Measure.restrict_eq_self_of_ae_mem hae
  refine ⟨U,hA.inter hB,inter_subset_left,hμ,?_⟩
  intro ω hω
  have hp : (μ.restrict A) {ω' | code ω'=code ω} ≠ 0 := hω.2
  have hclass : MeasurableSet {ω' | code ω'=code ω} :=
    hcode (measurableSet_singleton (code ω))
  rw [Measure.restrict_apply hclass,inter_comm] at hp
  exact hp

end Submission.Lib.K4ScalarCoreAssembly
