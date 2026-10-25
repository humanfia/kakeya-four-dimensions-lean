/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit b8fcf4469310bc1c6f7304993f7192e4f485e568,
Submission/Obl/k4_scalar_mesh_projection/ActualCoordinates.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.ActualFourStep
import Submission.Lib.K4ScalarActualSwitching.PathCoordinates

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable def actualPathCoordinates {X : Type*} [MeasurableSpace X]
    (control : X → ℝ)
    (z : (((((X × ℝ) × (X × ℝ)) × (X × ℝ)) × (X × ℝ)) × (X × ℝ))) :
    ((X × ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) :=
  pathIncrementCoordinates Prod.snd
    (Prod.map (Prod.map (Prod.map (Prod.map id (Prod.map control id))
      (Prod.map control id)) (Prod.map control id)) (Prod.map control id) z)

theorem measurable_actualPathCoordinates {X : Type*} [MeasurableSpace X]
    (control : X → ℝ) (hcontrol : Measurable control) : Measurable (actualPathCoordinates control) := by
  have hobs : Measurable (Prod.map control (id : ℝ → ℝ)) := hcontrol.prodMap measurable_id
  exact (measurePreserving_pathIncrementCoordinates (0 : Measure (X × ℝ)) volume
    Prod.snd measurable_snd).measurable.comp
      ((((measurable_id.prodMap hobs).prodMap hobs).prodMap hobs).prodMap hobs)

theorem actualPathCoordinates_apply {X : Type*} [MeasurableSpace X]
    (control : X → ℝ)
    (z : (((((X × ℝ) × (X × ℝ)) × (X × ℝ)) × (X × ℝ)) × (X × ℝ))) :
    actualPathCoordinates control z =
      ((z.1.1.1.1, ![control z.1.1.1.2.1, control z.1.1.2.1, control z.1.2.1, control z.2.1]),
        ![z.1.1.1.2.2 - z.1.1.1.1.2, z.1.1.2.2 - z.1.1.1.2.2,
          z.1.2.2 - z.1.1.2.2, z.2.2 - z.1.2.2]) := by
  unfold actualPathCoordinates pathIncrementCoordinates
  rw [pathProductEquiv_apply]
  dsimp only [Prod.map]
  rw [Switching.signedIncrements_apply]
  rfl

theorem actualPathCoordinates_map_le {X : Type*} [MeasurableSpace X]
    (control : X → ℝ) (hcontrol : Measurable control)
    (μ : Measure (X × ℝ)) [SFinite μ] (π : Measure ℝ) [SigmaFinite π]
    (ρ : Measure (((((X × ℝ) × (X × ℝ)) × (X × ℝ)) × (X × ℝ)) × (X × ℝ)))
    (D : ENNReal)
    (hρ : ρ.map (Prod.map (Prod.map (Prod.map (Prod.map id (Prod.map control id))
      (Prod.map control id)) (Prod.map control id)) (Prod.map control id)) ≤ D •
      ((((μ.prod (π.prod volume)).prod (π.prod volume)).prod (π.prod volume)).prod (π.prod volume))) :
    ρ.map (actualPathCoordinates control) ≤
        D • ((μ.prod (Measure.pi (fun _ : Fin 4 => π))).prod volume) ∧
      ρ.map (actualPathCoordinates control) univ = ρ univ := by
  let obs := Prod.map control (id : ℝ → ℝ)
  let f := Prod.map (Prod.map (Prod.map (Prod.map (id : X × ℝ → X × ℝ) obs) obs) obs) obs
  have hobs : Measurable obs := hcontrol.prodMap measurable_id
  have hf : Measurable f := (((measurable_id.prodMap hobs).prodMap hobs).prodMap hobs).prodMap hobs
  have h := map_pathIncrementCoordinates_le μ π Prod.snd measurable_snd (ρ.map f) D hρ
  have hpath := (measurePreserving_pathIncrementCoordinates μ π Prod.snd measurable_snd).measurable
  have heq : (ρ.map f).map (pathIncrementCoordinates Prod.snd) =
      ρ.map (actualPathCoordinates control) := by
    rw [Measure.map_map hpath hf]
    rfl
  rw [heq] at h
  exact ⟨h.1, h.2.trans (by rw [Measure.map_apply hf MeasurableSet.univ, preimage_univ])⟩

/-- The complete stochastic input to the endpoint-volume argument: the
actual four-switch law in start/control/signed-increment coordinates,
with its original mass budget and original product reference. -/
theorem actual_four_step_increment_law {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [StandardBorelSpace (X × ℝ)] [Nonempty (X × ℝ)]
    (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X ℝ) [IsMarkovKernel κ]
    (state : X × ℝ → Q) (hstate : Measurable state)
    (control : X → ℝ) (hcontrol : Measurable control)
    (π : Measure ℝ) [SigmaFinite π]
    (L : Set X) (hL : MeasurableSet L) (K D p : ENNReal) (r : ℝ)
    (hrect : ∀ q (A : Set ℝ), MeasurableSet A →
      (ν ⊗ₘ κ) {ω | state ω = q ∧ control ω.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p)
    (htime : ∀ x ∈ L, κ x ≤ D • volume) :
    let μ := ν ⊗ₘ κ
    let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
    let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
    let ρ := θ₄.map (actualPathCoordinates control)
    μ univ ≤ ρ univ + 4 * μ (Prod.fst ⁻¹' Lᶜ) + 4 * (K * p) * μ univ ∧
      ρ ≤ (K * D) ^ 4 • ((μ.prod (Measure.pi (fun _ : Fin 4 => π))).prod volume) := by
  let μ := ν ⊗ₘ κ
  let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
  let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
  let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
  let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
  have hfour := actual_four_step_law ν κ state hstate control hcontrol π volume L hL K D p r
    hrect hthin htime
  have hmap := actualPathCoordinates_map_le control hcontrol μ π θ₄ ((K * D) ^ 4) hfour.2.2
  refine ⟨?_, hmap.1⟩
  change μ univ ≤ (θ₄.map (actualPathCoordinates control)) univ +
    4 * μ (Prod.fst ⁻¹' Lᶜ) + 4 * (K * p) * μ univ
  rw [hmap.2]
  exact hfour.2.1

end Submission.Lib.K4ScalarActualSwitching
