/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit b8fcf4469310bc1c6f7304993f7192e4f485e568,
Submission/Obl/k4_scalar_mesh_projection/ActualPathSupport.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.ActualFourStep

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem retainedActualSwitch_fst_le {H X T Q : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace Q]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (θ : Measure H) [SFinite θ] (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (current : H → X × T) (hcurrent : Measurable current)
    (control : X → ℝ) (L : Set X) (r : ℝ) :
    (retainedActualSwitch θ ν κ state hstate current hcurrent control L r).fst ≤ θ := by
  letI := stateTimeSwitch_markov ν κ state hstate
  unfold retainedActualSwitch
  exact (Measure.fst_mono Measure.restrict_le_self).trans_eq (Measure.fst_compProd _ _)

theorem retainedActualSwitch_ae_history {H X T Q : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace Q]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (θ : Measure H) [SFinite θ] (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (current : H → X × T) (hcurrent : Measurable current)
    (control : X → ℝ) (L : Set X) (r : ℝ)
    {P : H → Prop} (hP : ∀ᵐ h ∂θ, P h) :
    ∀ᵐ z ∂retainedActualSwitch θ ν κ state hstate current hcurrent control L r, P z.1 :=
  ae_of_ae_map measurable_fst.aemeasurable
    (ae_mono (retainedActualSwitch_fst_le θ ν κ state hstate current hcurrent control L r) hP)

theorem retainedActualSwitch_ae_good {H X T Q : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace Q]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (θ : Measure H) (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (current : H → X × T) (hcurrent : Measurable current)
    (control : X → ℝ) (hcontrol : Measurable control)
    (L : Set X) (hL : MeasurableSet L) (r : ℝ) :
    ∀ᵐ z ∂retainedActualSwitch θ ν κ state hstate current hcurrent control L r,
      z.2.1 ∈ L ∧ r ≤ |control z.2.1 - control (current z.1).1| := by
  unfold retainedActualSwitch
  apply ae_restrict_mem
  exact (hL.preimage (measurable_fst.comp measurable_snd)).inter
    (measurableSet_le measurable_const
      ((hcontrol.comp (measurable_fst.comp measurable_snd)).sub
        (hcontrol.comp (measurable_fst.comp (hcurrent.comp measurable_fst)))).abs)

/-- Every measurable geometric relation certified by the shared state
holds for the actual new line at every retained step. -/
theorem retainedActualSwitch_ae_relation {H X T Q : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace T] [MeasurableSpace Q] [StandardBorelSpace Q]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (θ : Measure H) [SFinite θ] (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (current : H → X × T) (hcurrent : Measurable current)
    (hmarg : θ.map current ≤ ν ⊗ₘ κ)
    (control : X → ℝ) (L : Set X) (r : ℝ)
    (R : (X × T) → X → Prop) (hR : MeasurableSet {z : (X × T) × X | R z.1 z.2})
    (hcert : ∀ ω z, state z = state ω → R ω z.1) :
    ∀ᵐ z ∂retainedActualSwitch θ ν κ state hstate current hcurrent control L r,
      R (current z.1) z.2.1 := by
  have hrel := stateTimeSwitch_ae_line_relation ν κ state hstate R
    (fun ω => hR.preimage (measurable_const.prodMk measurable_id)) hcert
  have hpull := ae_of_ae_map hcurrent.aemeasurable (ae_mono hmarg hrel)
  have hfull : ∀ᵐ z ∂(θ ⊗ₘ (stateTimeSwitch ν κ state hstate).comap current hcurrent),
      R (current z.1) z.2.1 := by
    apply Measure.ae_compProd_of_ae_ae
      (hR.preimage ((hcurrent.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)))
    exact hpull
  exact ae_mono Measure.restrict_le_self hfull

/-- The two velocity bases used by the four-leg endpoint determinant
hold for the actual retained four-step law. -/
theorem actual_four_step_control_bases {X T Q : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace Q]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (control : X → ℝ) (hcontrol : Measurable control)
    (L : Set X) (hL : MeasurableSet L) (r : ℝ) :
    let μ := ν ⊗ₘ κ
    let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
    let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
    ∀ᵐ z ∂θ₄,
      r ≤ |control z.1.1.2.1 - control z.1.1.1.2.1| ∧
        r ≤ |control z.2.1 - control z.1.2.1| := by
  let μ := ν ⊗ₘ κ
  letI := stateTimeSwitch_markov ν κ state hstate
  let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
  letI : IsFiniteMeasure θ₁ := by dsimp only [θ₁, retainedActualSwitch]; infer_instance
  let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₂ := by dsimp only [θ₂, retainedActualSwitch]; infer_instance
  let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₃ := by dsimp only [θ₃, retainedActualSwitch]; infer_instance
  let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
  have h₂ := retainedActualSwitch_ae_good θ₁ ν κ state hstate Prod.snd measurable_snd
    control hcontrol L hL r
  have h₃ := retainedActualSwitch_ae_history θ₂ ν κ state hstate Prod.snd measurable_snd
    control L r h₂
  have h₄ := retainedActualSwitch_ae_history θ₃ ν κ state hstate Prod.snd measurable_snd
    control L r h₃
  have hlast := retainedActualSwitch_ae_good θ₃ ν κ state hstate Prod.snd measurable_snd
    control hcontrol L hL r
  change ∀ᵐ z ∂θ₄,
    r ≤ |control z.1.1.2.1 - control z.1.1.1.2.1| ∧
      r ≤ |control z.2.1 - control z.1.2.1|
  filter_upwards [h₄, hlast] with z hz hl
  exact ⟨hz.2, hl.2⟩

end Submission.Lib.K4ScalarActualSwitching
