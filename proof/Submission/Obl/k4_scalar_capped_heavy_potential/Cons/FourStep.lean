import Submission.Lib.K4ScalarActualSwitching

/-!
# The four-switch path law, packaged

The accepted `K4ScalarActualSwitching` constructs the genuine four-switch
history law (state redraw, then a fresh time on the new line, four times),
with its retained-mass budget, its product ceiling in normalized increment
coordinates, the almost-everywhere transfer of incidence properties to all
five states, the shared-state line relations, and the two separated control
bases. This file collects these facts about one history law `θ`.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory ProbabilityTheory
open Submission.Lib.K4ScalarActualSwitching

/-- The type of five-incidence switch histories. -/
abbrev History (X : Type*) := ((((X × ℝ) × (X × ℝ)) × (X × ℝ)) × (X × ℝ)) × (X × ℝ)

/-- All facts about the four-switch history law used by the curl estimate. -/
theorem four_step_package {X Q : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q] [StandardBorelSpace Q]
    [StandardBorelSpace (X × ℝ)] [Nonempty (X × ℝ)]
    (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X ℝ) [IsMarkovKernel κ]
    (state : X × ℝ → Q) (hstate : Measurable state)
    (control : X → ℝ) (hcontrol : Measurable control)
    (π : Measure ℝ) [SigmaFinite π]
    (L : Set X) (hL : MeasurableSet L) (K D p : ENNReal) (r h : ℝ) (hh : 0 < h)
    (hrect : ∀ q (A : Set ℝ), MeasurableSet A →
      (ν ⊗ₘ κ) {ω | state ω = q ∧ control ω.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p)
    (htime : ∀ x ∈ L, κ x ≤ ((ENNReal.ofReal h)⁻¹ * D) • volume) :
    ∃ θ : Measure (History X), IsFiniteMeasure θ ∧
      (ν ⊗ₘ κ) univ ≤ θ univ + 4 * (ν ⊗ₘ κ) (Prod.fst ⁻¹' Lᶜ) + 4 * (K * p) * (ν ⊗ₘ κ) univ ∧
      (θ.map (actualPathCoordinates control)).map (normalizeIncrements h) ≤
        (K * D) ^ 4 • (((ν ⊗ₘ κ).prod (Measure.pi fun _ : Fin 4 => π)).prod volume) ∧
      (∀ P : X × ℝ → Prop, (∀ᵐ ω ∂(ν ⊗ₘ κ), P ω) →
        ∀ᵐ z ∂θ, P z.1.1.1.1 ∧ P z.1.1.1.2 ∧ P z.1.1.2 ∧ P z.1.2 ∧ P z.2) ∧
      (∀ R : (X × ℝ) → X → Prop, MeasurableSet {z : (X × ℝ) × X | R z.1 z.2} →
        (∀ ω z, state z = state ω → R ω z.1) →
        ∀ᵐ z ∂θ, R z.1.1.1.1 z.1.1.1.2.1 ∧ R z.1.1.1.2 z.1.1.2.1 ∧
          R z.1.1.2 z.1.2.1 ∧ R z.1.2 z.2.1) ∧
      (∀ᵐ z ∂θ, r ≤ |control z.1.1.2.1 - control z.1.1.1.2.1| ∧
        r ≤ |control z.2.1 - control z.1.2.1|) := by
  let μ := ν ⊗ₘ κ
  letI := stateTimeSwitch_markov ν κ state hstate
  let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
  letI : IsFiniteMeasure θ₁ := by dsimp only [θ₁, retainedActualSwitch]; infer_instance
  let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₂ := by dsimp only [θ₂, retainedActualSwitch]; infer_instance
  let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₃ := by dsimp only [θ₃, retainedActualSwitch]; infer_instance
  let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
  letI : IsFiniteMeasure θ₄ := by dsimp only [θ₄, retainedActualSwitch]; infer_instance
  have hlaw := actual_four_step_normalized_increment_law ν κ state hstate control hcontrol π L hL
    K D p r h hh hrect hthin htime
  have hunivmap : ((θ₄.map (actualPathCoordinates control)).map (normalizeIncrements h)) univ =
      θ₄ univ := by
    rw [Measure.map_apply (measurable_normalizeIncrements h) MeasurableSet.univ, preimage_univ,
      Measure.map_apply (measurable_actualPathCoordinates control hcontrol) MeasurableSet.univ,
      preimage_univ]
  have hmass := hlaw.1
  rw [hunivmap] at hmass
  refine ⟨θ₄, inferInstance, hmass, hlaw.2, ?_, ?_, ?_⟩
  · intro P hP
    exact actual_four_step_ae_states ν κ state hstate control L r P hP
  · intro R hR hcert
    exact actual_four_step_ae_relations ν κ state hstate control L r R hR hcert
  · exact actual_four_step_control_bases ν κ state hstate control hcontrol L hL r

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
