/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit b8fcf4469310bc1c6f7304993f7192e4f485e568,
Submission/Obl/k4_scalar_mesh_projection/ActualGeometry.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.ActualCoordinates
import Submission.Lib.K4ScalarActualSwitching.ActualPathSupport

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem retainedActualSwitch_snd_le {H X T Q : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace Q]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (θ : Measure H) [SFinite θ] (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (current : H → X × T) (hcurrent : Measurable current)
    (hmarg : θ.map current ≤ ν ⊗ₘ κ)
    (control : X → ℝ) (L : Set X) (r : ℝ) :
    (retainedActualSwitch θ ν κ state hstate current hcurrent control L r).snd ≤ ν ⊗ₘ κ := by
  letI := stateTimeSwitch_markov ν κ state hstate
  unfold retainedActualSwitch
  exact (Measure.snd_mono Measure.restrict_le_self).trans
    (stationary_history_snd_le θ (ν ⊗ₘ κ) current hcurrent
      (stateTimeSwitch ν κ state hstate) (stateTimeSwitch_invariant ν κ state hstate) hmarg)

/-- Every original a.e. incidence property holds at every one of the
five actual states in the retained four-switch history. -/
theorem actual_four_step_ae_states {X T Q : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace Q]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (control : X → ℝ) (L : Set X) (r : ℝ)
    (P : X × T → Prop) (hP : ∀ᵐ ω ∂(ν ⊗ₘ κ), P ω) :
    let μ := ν ⊗ₘ κ
    let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
    let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
    ∀ᵐ z ∂θ₄, P z.1.1.1.1 ∧ P z.1.1.1.2 ∧ P z.1.1.2 ∧ P z.1.2 ∧ P z.2 := by
  let μ := ν ⊗ₘ κ
  letI := stateTimeSwitch_markov ν κ state hstate
  let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
  letI : IsFiniteMeasure θ₁ := by dsimp only [θ₁, retainedActualSwitch]; infer_instance
  let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₂ := by dsimp only [θ₂, retainedActualSwitch]; infer_instance
  let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₃ := by dsimp only [θ₃, retainedActualSwitch]; infer_instance
  let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
  have hd₁ := retainedActualSwitch_snd_le μ ν κ state hstate id measurable_id
    (by change μ.map id ≤ μ; simp) control L r
  have hd₂ := retainedActualSwitch_snd_le θ₁ ν κ state hstate Prod.snd measurable_snd hd₁ control L r
  have hd₃ := retainedActualSwitch_snd_le θ₂ ν κ state hstate Prod.snd measurable_snd hd₂ control L r
  have hd₄ := retainedActualSwitch_snd_le θ₃ ν κ state hstate Prod.snd measurable_snd hd₃ control L r
  have h₁ : ∀ᵐ z ∂θ₁, P z.1 ∧ P z.2 := by
    filter_upwards [retainedActualSwitch_ae_history μ ν κ state hstate id measurable_id control L r hP,
      ae_of_ae_map measurable_snd.aemeasurable (ae_mono hd₁ hP)] with z hp hn
    exact ⟨hp, hn⟩
  have h₂ : ∀ᵐ z ∂θ₂, P z.1.1 ∧ P z.1.2 ∧ P z.2 := by
    filter_upwards [retainedActualSwitch_ae_history θ₁ ν κ state hstate Prod.snd measurable_snd
      control L r h₁, ae_of_ae_map measurable_snd.aemeasurable (ae_mono hd₂ hP)] with z hp hn
    exact ⟨hp.1, hp.2, hn⟩
  have h₃ : ∀ᵐ z ∂θ₃, P z.1.1.1 ∧ P z.1.1.2 ∧ P z.1.2 ∧ P z.2 := by
    filter_upwards [retainedActualSwitch_ae_history θ₂ ν κ state hstate Prod.snd measurable_snd
      control L r h₂, ae_of_ae_map measurable_snd.aemeasurable (ae_mono hd₃ hP)] with z hp hn
    exact ⟨hp.1, hp.2.1, hp.2.2, hn⟩
  change ∀ᵐ z ∂θ₄, P z.1.1.1.1 ∧ P z.1.1.1.2 ∧ P z.1.1.2 ∧ P z.1.2 ∧ P z.2
  filter_upwards [retainedActualSwitch_ae_history θ₃ ν κ state hstate Prod.snd measurable_snd
    control L r h₃, ae_of_ae_map measurable_snd.aemeasurable (ae_mono hd₄ hP)] with z hp hn
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hn⟩

theorem actual_four_step_increment_bases {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q]
    [StandardBorelSpace (X × ℝ)] [Nonempty (X × ℝ)]
    (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X ℝ) [IsMarkovKernel κ]
    (state : X × ℝ → Q) (hstate : Measurable state)
    (control : X → ℝ) (hcontrol : Measurable control)
    (L : Set X) (hL : MeasurableSet L) (r : ℝ) :
    let μ := ν ⊗ₘ κ
    let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
    let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
    ∀ᵐ z ∂θ₄.map (actualPathCoordinates control),
      r ≤ |z.1.2 1 - z.1.2 0| ∧ r ≤ |z.1.2 3 - z.1.2 2| := by
  have hmeas : MeasurableSet {z : ((X × ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) |
      r ≤ |z.1.2 1 - z.1.2 0| ∧ r ≤ |z.1.2 3 - z.1.2 2|} := by
    have hv (i : Fin 4) : Measurable (fun z : ((X × ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
        z.1.2 i) := by fun_prop
    exact (measurableSet_le measurable_const ((hv 1).sub (hv 0)).abs).inter
      (measurableSet_le measurable_const ((hv 3).sub (hv 2)).abs)
  apply (ae_map_iff (measurable_actualPathCoordinates control hcontrol).aemeasurable hmeas).mpr
  filter_upwards [actual_four_step_control_bases ν κ state hstate control hcontrol L hL r] with z hz
  simpa [actualPathCoordinates_apply] using hz

theorem actual_four_step_increment_box_and_controls {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q]
    [StandardBorelSpace (X × ℝ)] [Nonempty (X × ℝ)]
    (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X ℝ) [IsMarkovKernel κ]
    (state : X × ℝ → Q) (hstate : Measurable state)
    (control : X → ℝ) (hcontrol : Measurable control)
    (L : Set X) (r a q K : ℝ)
    (hdata : ∀ᵐ ω ∂(ν ⊗ₘ κ), ω.2 ∈ Icc a (a + q) ∧ |control ω.1| ≤ K) :
    let μ := ν ⊗ₘ κ
    let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
    let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
    ∀ᵐ z ∂θ₄.map (actualPathCoordinates control),
      z.2 ∈ Icc (fun _ => -q) (fun _ => q) ∧ ∀ i, |z.1.2 i| ≤ K := by
  have hmeas : MeasurableSet {z : ((X × ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) |
      z.2 ∈ Icc (fun _ => -q) (fun _ => q) ∧ ∀ i, |z.1.2 i| ≤ K} := by
    apply (measurableSet_Icc.preimage measurable_snd).inter
    have hv (i : Fin 4) : Measurable (fun z : ((X × ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
        z.1.2 i) := by fun_prop
    have hAll := MeasurableSet.iInter (fun i : Fin 4 =>
      measurableSet_le (hv i).abs (measurable_const (a := K)))
    rw [← Set.ofPred_forall] at hAll
    simpa only [Set.ofPred] using hAll
  apply (ae_map_iff (measurable_actualPathCoordinates control hcontrol).aemeasurable hmeas).mpr
  filter_upwards [actual_four_step_ae_states ν κ state hstate control L r
    (fun ω => ω.2 ∈ Icc a (a + q) ∧ |control ω.1| ≤ K) hdata] with z hz
  have ht : ∀ i : Fin 4,
      (![z.1.1.1.2.2, z.1.1.2.2, z.1.2.2, z.2.2] : Fin 4 → ℝ) i ∈ Icc a (a + q) := by
    intro i
    fin_cases i
    · exact hz.2.1.1
    · exact hz.2.2.1.1
    · exact hz.2.2.2.1.1
    · exact hz.2.2.2.2.1
  rw [actualPathCoordinates_apply]
  constructor
  · simpa [Switching.signedIncrements_apply] using Switching.signedIncrements_mem_cube hz.1.1 _ ht
  · intro i
    fin_cases i
    · exact hz.2.1.2
    · exact hz.2.2.1.2
    · exact hz.2.2.2.1.2
    · exact hz.2.2.2.2.2

/-- All four new lines satisfy the geometric relations certified at
their actual shared states, within the same retained path law. -/
theorem actual_four_step_ae_relations {X T Q : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace T]
    [MeasurableSpace Q] [StandardBorelSpace Q]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (control : X → ℝ) (L : Set X) (r : ℝ)
    (R : (X × T) → X → Prop) (hR : MeasurableSet {z : (X × T) × X | R z.1 z.2})
    (hcert : ∀ ω z, state z = state ω → R ω z.1) :
    let μ := ν ⊗ₘ κ
    let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
    let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
    ∀ᵐ z ∂θ₄,
      R z.1.1.1.1 z.1.1.1.2.1 ∧ R z.1.1.1.2 z.1.1.2.1 ∧
        R z.1.1.2 z.1.2.1 ∧ R z.1.2 z.2.1 := by
  let μ := ν ⊗ₘ κ
  letI := stateTimeSwitch_markov ν κ state hstate
  let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
  letI : IsFiniteMeasure θ₁ := by dsimp only [θ₁, retainedActualSwitch]; infer_instance
  let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₂ := by dsimp only [θ₂, retainedActualSwitch]; infer_instance
  let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₃ := by dsimp only [θ₃, retainedActualSwitch]; infer_instance
  let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
  have hstart : μ.map id ≤ μ := by simp
  have hd₁ := retainedActualSwitch_snd_le μ ν κ state hstate id measurable_id hstart control L r
  have hd₂ := retainedActualSwitch_snd_le θ₁ ν κ state hstate Prod.snd measurable_snd hd₁ control L r
  have hd₃ := retainedActualSwitch_snd_le θ₂ ν κ state hstate Prod.snd measurable_snd hd₂ control L r
  have h₁ := retainedActualSwitch_ae_relation μ ν κ state hstate id measurable_id
    hstart control L r R hR hcert
  have h₂ : ∀ᵐ z ∂θ₂, R z.1.1 z.1.2.1 ∧ R z.1.2 z.2.1 := by
    filter_upwards [retainedActualSwitch_ae_history θ₁ ν κ state hstate Prod.snd measurable_snd
      control L r h₁, retainedActualSwitch_ae_relation θ₁ ν κ state hstate Prod.snd measurable_snd
        hd₁ control L r R hR hcert] with z hp hn
    exact ⟨hp, hn⟩
  have h₃ : ∀ᵐ z ∂θ₃, R z.1.1.1 z.1.1.2.1 ∧ R z.1.1.2 z.1.2.1 ∧ R z.1.2 z.2.1 := by
    filter_upwards [retainedActualSwitch_ae_history θ₂ ν κ state hstate Prod.snd measurable_snd
      control L r h₂, retainedActualSwitch_ae_relation θ₂ ν κ state hstate Prod.snd measurable_snd
        hd₂ control L r R hR hcert] with z hp hn
    exact ⟨hp.1, hp.2, hn⟩
  change ∀ᵐ z ∂θ₄,
    R z.1.1.1.1 z.1.1.1.2.1 ∧ R z.1.1.1.2 z.1.1.2.1 ∧ R z.1.1.2 z.1.2.1 ∧ R z.1.2 z.2.1
  filter_upwards [retainedActualSwitch_ae_history θ₃ ν κ state hstate Prod.snd measurable_snd
    control L r h₃, retainedActualSwitch_ae_relation θ₃ ν κ state hstate Prod.snd measurable_snd
      hd₃ control L r R hR hcert] with z hp hn
  exact ⟨hp.1, hp.2.1, hp.2.2, hn⟩

end Submission.Lib.K4ScalarActualSwitching
