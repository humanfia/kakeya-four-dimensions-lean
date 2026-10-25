import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathViews
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensityMasks
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.FiniteViews
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.WorldSupport
import Submission.Obl.k4_scalar_guarded_entropic_path.ChartLayer

/-! Choose all candidate-parent root charts before sampling the common
residual. Early unavailable entries are empty layers. Narrow-row events
in every view have power-small mass on the same final probability. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalView

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)
open TrueLiftChains PathMeasures IntermediateLiftSupport
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

variable {root final : Code} {D S₀ η : ℝ}

abbrev ChartAt (a : OriginalView root final D S₀ η) (ε : ℝ) (k : ℕ) (j : Fin a.count) :=
  ChartW a.parent a.complexity (a.depth j) (L a.parent) (a.time j + ε) ε true
    (a.suffixChain.sample k)

def GoodCharts (a : OriginalView root final D S₀ η) (ε : ℝ) (k : ℕ) : Prop :=
  ∀ j : Fin a.count, ∃ P : a.ChartAt ε k j,
    ChartGeometry.ofChart P = a.geometry k j ∧
    ∀ ρ : Measure (Fin (W final k) × State), ρ ≪ worldMixture final k →
      ∀ᵐ u ∂ρ.map (a.suffixChain.pullback k), u ∈ chartRegion P

/-- This choice precedes every residual on the fixed final measure. -/
def chartChoice (a : OriginalView root final D S₀ η) (ε : ℝ) (j : Fin a.count) (k : ℕ) :
    Option (a.ChartAt ε k j) := by
  classical
  exact if hk : a.GoodCharts ε k then some (Classical.choose (hk j)) else none

def layerAt (a : OriginalView root final D S₀ η) (ε : ℝ) (j : Fin a.count) (k : ℕ) :
    Layer (a.parent.1 (a.suffixChain.sample k)) :=
  match a.chartChoice ε j k with
  | none => Layer.empty _
  | some P => Layer.ofChart P

def LayerValid (a : OriginalView root final D S₀ η) (ε : ℝ) (j : Fin a.count) (k : ℕ)
    (F : Layer (a.parent.1 (a.suffixChain.sample k))) : Prop :=
  WidthGeometry.ChartData a.parent a.complexity (a.depth j) (L a.parent)
    (a.time j + ε) ε true (a.suffixChain.sample k) F.T F.n F.world F.block
    F.assignment F.witness F.u F.v F.width F.graph F.list

theorem layerAt_of_choice (a : OriginalView root final D S₀ η) (ε : ℝ) (j : Fin a.count)
    (k : ℕ) (P : a.ChartAt ε k j) (hchoice : a.chartChoice ε j k = some P) :
    a.layerAt ε j k = Layer.ofChart P := by
  rw [layerAt, hchoice]

/-- A realized choice retains its immutable geometry and its universal
original support, even after the final residual has been selected. -/
theorem chartChoice_spec (a : OriginalView root final D S₀ η) (ε : ℝ) (j : Fin a.count)
    (k : ℕ) (P : a.ChartAt ε k j) (hchoice : a.chartChoice ε j k = some P) :
    ChartGeometry.ofChart P = a.geometry k j ∧
      ∀ ρ : Measure (Fin (W final k) × State), ρ ≪ worldMixture final k →
        ∀ᵐ u ∂ρ.map (a.suffixChain.pullback k), u ∈ chartRegion P := by
  classical
  unfold chartChoice at hchoice
  split_ifs at hchoice with hk
  · have heq : Classical.choose (hk j) = P := Option.some.inj hchoice
    simpa only [heq] using Classical.choose_spec (hk j)

theorem eventually_chartChoice (a : OriginalView root final D S₀ η) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ j : Fin a.count, ∃ P : a.ChartAt ε k j,
      a.chartChoice ε j k = some P ∧
      ChartGeometry.ofChart P = a.geometry k j ∧
      ∀ ρ : Measure (Fin (W final k) × State), ρ ≪ worldMixture final k →
        ∀ᵐ u ∂ρ.map (a.suffixChain.pullback k), u ∈ chartRegion P := by
  classical
  filter_upwards [a.layers ε hε] with k hk
  intro j
  have hgood : a.GoodCharts ε k := hk
  refine ⟨Classical.choose (hk j), ?_, Classical.choose_spec (hk j)⟩
  unfold chartChoice
  rw [dite_eq_left hgood]

/-- The original tagged exception remains measurable even before the
root charts become available, when its layer is empty. -/
theorem measurableSet_narrow (a : OriginalView root final D S₀ η) (ε u : ℝ)
    (j : Fin a.count) (k : ℕ) (g : Fin (W a.parent (a.suffixChain.sample k))) :
    MeasurableSet (WidthGeometry.narrowEvent (a.layerAt ε j k) ε u g) := by
  cases hc : a.chartChoice ε j k with
  | none =>
    have heq : a.layerAt ε j k = Layer.empty _ := by rw [layerAt, hc]
    rw [heq]
    simp [Layer.empty, WidthGeometry.narrowEvent]
  | some P =>
    rw [a.layerAt_of_choice ε j k P hc]
    exact WidthGeometry.measurableSet_narrowEvent (F := Layer.ofChart P) P.hcd u g

theorem measurableSet_narrowTagged (a : OriginalView root final D S₀ η) (ε u : ℝ)
    (j : Fin a.count) (k : ℕ) :
    MeasurableSet (taggedEvent (WidthGeometry.narrowEvent (a.layerAt ε j k) ε u)) :=
  measurableSet_taggedEvent _ (a.measurableSet_narrow ε u j k)

set_option backward.isDefEq.respectTransparency false in
/-- The original exception in ANY candidate parent is power-small in
the common exact resolution, uniformly over the final sample tail. -/
theorem narrowTagged_powerSmall (a : OriginalView root final D S₀ η) (ε u : ℝ)
    (hε : 0 < ε) (hu : 0 < u) (huU : u ≤ U a.parent)
    (hεsmall : ε ≤ S a.parent * u / 4) (j : Fin a.count) :
    IsPowerSmall (N final) (fun k => worldMixture a.parent (a.suffixChain.sample k)
      (taggedEvent (WidthGeometry.narrowEvent (a.layerAt ε j k) ε u))) := by
  have hchart : ∀ᶠ k in atTop,
      WidthGeometry.ChartData a.parent a.complexity (a.depth j) (L a.parent)
        (a.time j + ε) ε true (a.suffixChain.sample k)
        (a.layerAt ε j k).T (a.layerAt ε j k).n (a.layerAt ε j k).world
        (a.layerAt ε j k).block (a.layerAt ε j k).assignment (a.layerAt ε j k).witness
        (a.layerAt ε j k).u (a.layerAt ε j k).v (a.layerAt ε j k).width
        (a.layerAt ε j k).graph (a.layerAt ε j k).list := by
    filter_upwards [a.eventually_chartChoice ε hε] with k hk
    obtain ⟨P, hP, _⟩ := hk j
    change a.LayerValid ε j k (a.layerAt ε j k)
    rw [a.layerAt_of_choice ε j k P hP]
    exact P.hcd
  obtain ⟨c, hc, hb⟩ := WidthGeometry.narrowEvent_powerSmall a.parent_exact
    a.suffixChain.sample a.suffixChain.sample_strictMono a.complexity
    (fun _ => a.depth j) (fun _ => a.time j + ε) (fun _ => ε) true
    (a.layerAt ε j) hchart hu huU (Eventually.of_forall fun _ => hεsmall)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hb] with k hk
  rw [a.suffixChain.resolution k]
  calc
    _ = ∑ g, ENNReal.ofReal (ω a.parent (a.suffixChain.sample k) g) *
        mu a.parent (a.suffixChain.sample k) g
          (WidthGeometry.narrowEvent (a.layerAt ε j k) ε u g) :=
      worldMixture_taggedEvent a.parent (a.suffixChain.sample k) _ (a.measurableSet_narrow ε u j k)
    _ ≤ _ := by
      simpa only [WidthGeometry.RawData.weight, WidthGeometry.RawData.N, WidthGeometry.mu,
        ω, N, W, Code.weight, Code.N] using hk

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalView
