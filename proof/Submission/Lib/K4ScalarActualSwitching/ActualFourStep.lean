/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 9a98134f7426729d513297455b610395ba5215bf,
Submission/Obl/k4_scalar_mesh_projection/ActualFourStep.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.ActualPaths

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- Append an actual switch and retain its long-row, separated-control
outcomes, keeping the whole preceding incidence history. -/
noncomputable def retainedActualSwitch {H X T Q : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace Q]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (θ : Measure H) (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (current : H → X × T) (hcurrent : Measurable current)
    (control : X → ℝ) (L : Set X) (r : ℝ) : Measure (H × (X × T)) :=
  (θ ⊗ₘ (stateTimeSwitch ν κ state hstate).comap current hcurrent).restrict
    {z | z.2.1 ∈ L ∧ r ≤ |control z.2.1 - control (current z.1).1|}

/-- Four genuine switches retain mass after only the stated short-row
and pencil losses, and have the product start/control/time ceiling. -/
theorem actual_four_step_law {X T Q : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (control : X → ℝ) (hcontrol : Measurable control)
    (π : Measure ℝ) [SFinite π] (τ : Measure T) [SFinite τ]
    (L : Set X) (hL : MeasurableSet L) (K D p : ENNReal) (r : ℝ)
    (hrect : ∀ q (A : Set ℝ), MeasurableSet A →
      (ν ⊗ₘ κ) {ω | state ω = q ∧ control ω.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p)
    (htime : ∀ x ∈ L, κ x ≤ D • τ) :
    let μ := ν ⊗ₘ κ
    let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
    let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
    let obs : X × T → ℝ × T := Prod.map control id
    θ₄.snd ≤ μ ∧
      μ univ ≤ θ₄ univ + 4 * μ (Prod.fst ⁻¹' Lᶜ) + 4 * (K * p) * μ univ ∧
      θ₄.map (Prod.map (Prod.map (Prod.map (Prod.map id obs) obs) obs) obs) ≤
        (K * D) ^ 4 • (((μ.prod (π.prod τ)).prod (π.prod τ)).prod (π.prod τ)).prod (π.prod τ) := by
  let μ := ν ⊗ₘ κ
  let transition := stateTimeSwitch ν κ state hstate
  letI : IsMarkovKernel transition := stateTimeSwitch_markov ν κ state hstate
  let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
  letI : IsFiniteMeasure θ₁ := by dsimp only [θ₁, retainedActualSwitch]; infer_instance
  let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₂ := by dsimp only [θ₂, retainedActualSwitch]; infer_instance
  let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₃ := by dsimp only [θ₃, retainedActualSwitch]; infer_instance
  let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
  let obs : X × T → ℝ × T := Prod.map control id
  let f₁ := Prod.map (id : X × T → X × T) obs
  let f₂ := Prod.map f₁ obs
  let f₃ := Prod.map f₂ obs
  let f₄ := Prod.map f₃ obs
  have hobs : Measurable obs := hcontrol.prodMap measurable_id
  have hf₁ : Measurable f₁ := measurable_id.prodMap hobs
  have hf₂ : Measurable f₂ := hf₁.prodMap hobs
  have hf₃ : Measurable f₃ := hf₂.prodMap hobs
  have hold : Measurable (fun z : X × T => control z.1) := hcontrol.comp measurable_fst
  have h₀ := actual_switch_step μ ν κ state hstate id measurable_id
    (by change μ.map id ≤ μ; simp)
    id measurable_id μ 1 (by simp) control hcontrol (fun z => control z.1) hold
    π τ L hL K D p r hrect hthin htime
  change θ₁.snd ≤ μ ∧
    μ univ ≤ θ₁ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ ∧
    θ₁.map f₁ ≤ (1 * (K * D)) • μ.prod (π.prod τ) at h₀
  have h₁ := actual_switch_step θ₁ ν κ state hstate Prod.snd measurable_snd h₀.1
    f₁ hf₁ (μ.prod (π.prod τ)) (K * D) (by simpa only [one_mul] using h₀.2.2)
    control hcontrol (fun z => control z.2.1) (hold.comp measurable_snd)
    π τ L hL K D p r hrect hthin htime
  change θ₂.snd ≤ μ ∧
    θ₁ univ ≤ θ₂ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * θ₁ univ ∧
    θ₂.map f₂ ≤ ((K * D) * (K * D)) • (μ.prod (π.prod τ)).prod (π.prod τ) at h₁
  have h₂ := actual_switch_step θ₂ ν κ state hstate Prod.snd measurable_snd h₁.1
    f₂ hf₂ ((μ.prod (π.prod τ)).prod (π.prod τ)) ((K * D) * (K * D)) h₁.2.2
    control hcontrol (fun z => control z.2.1) (hold.comp measurable_snd)
    π τ L hL K D p r hrect hthin htime
  change θ₃.snd ≤ μ ∧
    θ₂ univ ≤ θ₃ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * θ₂ univ ∧
    θ₃.map f₃ ≤ ((K * D) * (K * D) * (K * D)) •
      ((μ.prod (π.prod τ)).prod (π.prod τ)).prod (π.prod τ) at h₂
  have h₃ := actual_switch_step θ₃ ν κ state hstate Prod.snd measurable_snd h₂.1
    f₃ hf₃ (((μ.prod (π.prod τ)).prod (π.prod τ)).prod (π.prod τ))
    ((K * D) * (K * D) * (K * D)) h₂.2.2
    control hcontrol (fun z => control z.2.1) (hold.comp measurable_snd)
    π τ L hL K D p r hrect hthin htime
  change θ₄.snd ≤ μ ∧
    θ₃ univ ≤ θ₄ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * θ₃ univ ∧
    θ₄.map f₄ ≤ ((K * D) * (K * D) * (K * D) * (K * D)) •
      (((μ.prod (π.prod τ)).prod (π.prod τ)).prod (π.prod τ)).prod (π.prod τ) at h₃
  have hm₁ : θ₁ univ ≤ μ univ := by
    simpa only [Measure.snd_apply MeasurableSet.univ, preimage_univ] using
      (Measure.le_iff.mp h₀.1 univ MeasurableSet.univ)
  have hm₂ : θ₂ univ ≤ μ univ := by
    simpa only [Measure.snd_apply MeasurableSet.univ, preimage_univ] using
      (Measure.le_iff.mp h₁.1 univ MeasurableSet.univ)
  have hm₃ : θ₃ univ ≤ μ univ := by
    simpa only [Measure.snd_apply MeasurableSet.univ, preimage_univ] using
      (Measure.le_iff.mp h₂.1 univ MeasurableSet.univ)
  have hb₀ : μ univ ≤ θ₁ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ := h₀.2.1
  have hb₁ : θ₁ univ ≤ θ₂ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ :=
    h₁.2.1.trans (add_le_add le_rfl (mul_le_mul' le_rfl hm₁))
  have hb₂ : θ₂ univ ≤ θ₃ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ :=
    h₂.2.1.trans (add_le_add le_rfl (mul_le_mul' le_rfl hm₂))
  have hb₃ : θ₃ univ ≤ θ₄ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ :=
    h₃.2.1.trans (add_le_add le_rfl (mul_le_mul' le_rfl hm₃))
  change θ₄.snd ≤ μ ∧
    μ univ ≤ θ₄ univ + 4 * μ (Prod.fst ⁻¹' Lᶜ) + 4 * (K * p) * μ univ ∧
    θ₄.map f₄ ≤ (K * D) ^ 4 •
      (((μ.prod (π.prod τ)).prod (π.prod τ)).prod (π.prod τ)).prod (π.prod τ)
  refine ⟨h₃.1, ?_, ?_⟩
  · calc
      μ univ ≤ θ₁ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ := hb₀
      _ ≤ (θ₂ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ) + μ (Prod.fst ⁻¹' Lᶜ) +
          (K * p) * μ univ := by gcongr
      _ ≤ ((θ₃ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ) + μ (Prod.fst ⁻¹' Lᶜ) +
          (K * p) * μ univ) + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ := by gcongr
      _ ≤ (((θ₄ univ + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ) + μ (Prod.fst ⁻¹' Lᶜ) +
          (K * p) * μ univ) + μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ) +
          μ (Prod.fst ⁻¹' Lᶜ) + (K * p) * μ univ := by gcongr
      _ = θ₄ univ + 4 * μ (Prod.fst ⁻¹' Lᶜ) + 4 * (K * p) * μ univ := by ring
  · have hpow : (K * D) * (K * D) * (K * D) * (K * D) = (K * D) ^ 4 := by ring
    simpa only [hpow] using h₃.2.2

end Submission.Lib.K4ScalarActualSwitching
