/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 9a98134f7426729d513297455b610395ba5215bf,
Submission/Obl/k4_scalar_mesh_projection/ActualPaths.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.CompleteSwitch
import Submission.Lib.K4ScalarActualSwitching.PaletteConditioning
import Submission.Lib.K4ScalarActualSwitching.RetainedProjection

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- A step of the genuine conditional switching experiment has both its
original retained-mass budget and its observed product ceiling. The
palette ceiling is derived from discrete-state rectangular caps. -/
theorem actual_switch_step {H X T Q Z : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace T]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace Z] [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (θ : Measure H) [SFinite θ]
    (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → Q) (hstate : Measurable state)
    (current : H → X × T) (hcurrent : Measurable current)
    (hmarg : θ.map current ≤ ν ⊗ₘ κ)
    (past : H → Z) (hpast : Measurable past)
    (σ : Measure Z) [SFinite σ] (K₀ : ENNReal) (hpastlaw : θ.map past ≤ K₀ • σ)
    (control : X → ℝ) (hcontrol : Measurable control)
    (old : H → ℝ) (hold : Measurable old)
    (π : Measure ℝ) [SFinite π] (τ : Measure T) [SFinite τ]
    (L : Set X) (hL : MeasurableSet L) (K D p : ENNReal) (r : ℝ)
    (hrect : ∀ q (A : Set ℝ), MeasurableSet A →
      (ν ⊗ₘ κ) {ω | state ω = q ∧ control ω.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p)
    (htime : ∀ x ∈ L, κ x ≤ D • τ) :
    let transition := stateTimeSwitch ν κ state hstate
    let G := {z : H × (X × T) | z.2.1 ∈ L ∧ r ≤ |control z.2.1 - old z.1|}
    let ρ := (θ ⊗ₘ transition.comap current hcurrent).restrict G
    ρ.snd ≤ ν ⊗ₘ κ ∧
      θ univ ≤ ρ univ + (ν ⊗ₘ κ) (Prod.fst ⁻¹' Lᶜ) + (K * p) * θ univ ∧
      ρ.map (Prod.map past (Prod.map control id)) ≤ (K₀ * (K * D)) • σ.prod (π.prod τ) := by
  let transition := stateTimeSwitch ν κ state hstate
  letI : IsMarkovKernel transition := stateTimeSwitch_markov ν κ state hstate
  let G := {z : H × (X × T) | z.2.1 ∈ L ∧ r ≤ |control z.2.1 - old z.1|}
  let ρ := (θ ⊗ₘ transition.comap current hcurrent).restrict G
  have hpalette := conditionalResampling_palette_le (ν ⊗ₘ κ) state hstate
    (fun ω => control ω.1) (hcontrol.comp measurable_fst) π K hrect
  let B : Set (X × T) := Prod.fst ⁻¹' Lᶜ
  have hB : MeasurableSet B := hL.compl.preimage measurable_fst
  have hbudget := stateTimeSwitch_good_step θ ν κ state hstate current hcurrent hmarg
    control hcontrol old hold π K p r hpalette hthin B hB
  have hG : {z : H × (X × T) | z.2 ∉ B ∧ r ≤ |control z.2.1 - old z.1|} = G := by
    ext z
    simp only [B, G, mem_ofPred_eq, mem_preimage, mem_compl_iff, not_not]
  simp only [hG] at hbudget
  have hcap := stateTimeSwitch_restricted_control_time_le ν κ state hstate control hcontrol
    π τ L hL K D hpalette htime
  have hpull : ∀ᵐ h ∂θ,
      ((transition (current h)).restrict (Prod.fst ⁻¹' L)).map (Prod.map control id) ≤
        (K * D) • π.prod τ :=
    ae_of_ae_map hcurrent.aemeasurable (ae_mono hmarg hcap)
  have hdom := retained_projected_history_le θ σ (π.prod τ)
    (transition.comap current hcurrent) past hpast (Prod.map control id)
    (hcontrol.prodMap measurable_id) (Prod.fst ⁻¹' L) (hL.preimage measurable_fst) G
    (fun _ hz => hz.1) K₀ (K * D) hpastlaw
    (by simpa only [Kernel.comap_apply] using hpull)
  exact ⟨hbudget.1, hbudget.2, hdom⟩

end Submission.Lib.K4ScalarActualSwitching
