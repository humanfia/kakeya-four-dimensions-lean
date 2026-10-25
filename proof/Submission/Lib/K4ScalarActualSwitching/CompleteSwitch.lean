/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 9a98134f7426729d513297455b610395ba5215bf,
Submission/Obl/k4_scalar_mesh_projection/CompleteSwitch.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarSwitching.Resampling
import Submission.Lib.K4ScalarActualSwitching.PaletteRefresh
import Submission.Lib.K4ScalarSwitching.StationaryPaths
import Submission.Lib.K4ScalarActualSwitching.RestrictedRefresh

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable def stateTimeSwitch {X T C : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace C]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (ν : Measure X) [IsFiniteMeasure ν] (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → C) (hstate : Measurable state) : Kernel (X × T) (X × T) :=
  lineRefreshKernel κ ∘ₖ conditionalResampling (ν ⊗ₘ κ) state hstate

theorem stateTimeSwitch_markov {X T C : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace C]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (ν : Measure X) [IsFiniteMeasure ν] (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → C) (hstate : Measurable state) :
    IsMarkovKernel (stateTimeSwitch ν κ state hstate) := by
  unfold stateTimeSwitch
  letI := lineRefreshKernel_markov κ
  letI := conditionalResampling_markov (ν ⊗ₘ κ) state hstate
  infer_instance

theorem stateTimeSwitch_invariant {X T C : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace C]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (ν : Measure X) [IsFiniteMeasure ν] (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → C) (hstate : Measurable state) :
    Kernel.Invariant (stateTimeSwitch ν κ state hstate) (ν ⊗ₘ κ) := by
  unfold stateTimeSwitch
  exact (lineRefreshKernel_invariant ν κ).comp
    (conditionalResampling_invariant (ν ⊗ₘ κ) state hstate)

/-- The line relation certified at the shared state survives the full time
refresh. The relation can express exact geometric incidence at the old time. -/
theorem stateTimeSwitch_ae_line_relation {X T C : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace T] [MeasurableSpace C] [StandardBorelSpace C]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (ν : Measure X) [IsFiniteMeasure ν] (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → C) (hstate : Measurable state)
    (R : (X × T) → X → Prop) (hR : ∀ ω, MeasurableSet {x | R ω x})
    (hcert : ∀ ω z, state z = state ω → R ω z.1) :
    ∀ᵐ ω ∂(ν ⊗ₘ κ), ∀ᵐ z ∂stateTimeSwitch ν κ state hstate ω, R ω z.1 := by
  filter_upwards [conditionalResampling_ae_key (ν ⊗ₘ κ) state hstate] with ω hω
  apply Kernel.ae_comp_of_ae_ae ((hR ω).preimage measurable_fst)
  filter_upwards [hω] with z hz
  filter_upwards [lineRefreshKernel_ae_line κ z] with z' hz'
  rw [hz']
  exact hcert ω z hz

/-- The genuine full switch, restricted to long rows, has the prepared
palette/time product ceiling. Short rows are deleted without normalization. -/
theorem stateTimeSwitch_restricted_control_time_le {X T C V : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace C] [MeasurableSpace V]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (ν : Measure X) [IsFiniteMeasure ν] (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → C) (hstate : Measurable state)
    (control : X → V) (hcontrol : Measurable control)
    (π : Measure V) [SFinite π] (τ : Measure T) [SFinite τ]
    (L : Set X) (hL : MeasurableSet L) (K D : ENNReal)
    (hpalette : ∀ᵐ ω ∂(ν ⊗ₘ κ),
      (conditionalResampling (ν ⊗ₘ κ) state hstate ω).map (fun z => control z.1) ≤ K • π)
    (hκ : ∀ x ∈ L, κ x ≤ D • τ) :
    ∀ᵐ ω ∂(ν ⊗ₘ κ),
      Measure.map (Prod.map control id)
        ((stateTimeSwitch ν κ state hstate ω).restrict (Prod.fst ⁻¹' L)) ≤
          (K * D) • π.prod τ := by
  let S := conditionalResampling (ν ⊗ₘ κ) state hstate
  letI := conditionalResampling_markov (ν ⊗ₘ κ) state hstate
  filter_upwards [hpalette] with ω hω
  have heq : stateTimeSwitch ν κ state hstate ω = lineRefreshKernel κ ∘ₘ S ω := by
    rw [stateTimeSwitch, Kernel.comp_apply]
  rw [heq]
  exact restricted_lineRefresh_control_time_le (S ω) π τ κ control hcontrol L hL K D hω
    (ae_of_all _ fun x hx => hκ x hx)

/-- The genuine state-conditional redraw followed by a line-preserving time
refresh has the stationary retained-mass budget used in a switched path.
The prepared palette bound is needed only a.e. for the incidence law. -/
theorem stateTimeSwitch_good_step {H X T C : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace C]
    [StandardBorelSpace (X × T)] [Nonempty (X × T)]
    (θ : Measure H) [SFinite θ]
    (ν : Measure X) [IsFiniteMeasure ν] (κ : Kernel X T) [IsMarkovKernel κ]
    (state : X × T → C) (hstate : Measurable state)
    (current : H → X × T) (hcurrent : Measurable current)
    (hmarg : θ.map current ≤ ν ⊗ₘ κ)
    (control : X → ℝ) (hcontrol : Measurable control)
    (old : H → ℝ) (hold : Measurable old)
    (π : Measure ℝ) (K p : ENNReal) (r : ℝ)
    (hpalette : ∀ᵐ ω ∂(ν ⊗ₘ κ),
      (conditionalResampling (ν ⊗ₘ κ) state hstate ω).map (fun z => control z.1) ≤ K • π)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p)
    (B : Set (X × T)) (hB : MeasurableSet B) :
    let transition := stateTimeSwitch ν κ state hstate
    let ρ := θ ⊗ₘ transition.comap current hcurrent
    let Good := {z : H × (X × T) | z.2 ∉ B ∧ r ≤ |control z.2.1 - old z.1|}
    (ρ.restrict Good).snd ≤ ν ⊗ₘ κ ∧
      θ univ ≤ (ρ.restrict Good) univ + (ν ⊗ₘ κ) B + (K * p) * θ univ := by
  let transition := stateTimeSwitch ν κ state hstate
  let S := conditionalResampling (ν ⊗ₘ κ) state hstate
  letI : IsMarkovKernel transition := stateTimeSwitch_markov ν κ state hstate
  have hinvariant : Kernel.Invariant transition (ν ⊗ₘ κ) :=
    stateTimeSwitch_invariant ν κ state hstate
  have hpull : ∀ᵐ h ∂θ, (S (current h)).map (fun z => control z.1) ≤ K • π :=
    ae_of_ae_map hcurrent.aemeasurable (ae_mono hmarg hpalette)
  have hpencil₀ := refreshed_pencil_bound θ (S.comap current hcurrent) κ
    control hcontrol old π K p r (by simpa only [Kernel.comap_apply] using hpull) hthin
  have hcomap : transition.comap current hcurrent =
      lineRefreshKernel κ ∘ₖ S.comap current hcurrent := by
    rw [← Kernel.comp_deterministic_eq_comap, ← Kernel.comp_deterministic_eq_comap,
      ← Kernel.comp_assoc]
    rfl
  let V : Set (H × (X × T)) := {z | |control z.2.1 - old z.1| < r}
  have hV : MeasurableSet V := by
    have hf : Measurable (fun z : H × (X × T) => |control z.2.1 - old z.1|) := by fun_prop
    exact measurableSet_lt hf measurable_const
  have hpencil : ∀ᵐ h ∂θ, transition (current h) (Prod.mk h ⁻¹' V) ≤ K * p := by
    filter_upwards [hpencil₀] with h hh
    change (transition.comap current hcurrent) h {z | |control z.1 - old h| < r} ≤ K * p
    rw [hcomap]
    exact hh
  have hh := stationary_history_good_step_ae θ (ν ⊗ₘ κ) current hcurrent
    transition hinvariant hmarg B hB V hV (K * p) hpencil
  simpa only [V, mem_ofPred_eq, not_lt] using hh

end Submission.Lib.K4ScalarActualSwitching
