import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CommonFloors
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootFloorCore

/-! The final common preparation is fixed before selecting a window.
It retains a quarter of the one final probability and all original floors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PreparedViews

open MeasureTheory Set Filter PathMeasures PathPruning
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {α : Type*} [Fintype α] {root final : Code} {D S₀ η : ℝ}

def FlooredCoreProperties (views : α → OriginalView root final D S₀ η)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent)
    (γ : ℝ) (k : ℕ) (E : Set (Fin (W final k) × State)) : Prop :=
  MeasurableSet E ∧ E ⊆ core views ε u tests k ∧
    ENNReal.ofReal (1 / 4 : ℝ) ≤ normalizedWorldMixture final k E ∧
    (∀ a j, ∃ P : (views a).ChartAt (ε a) k j,
      (views a).chartChoice (ε a) j k = some P ∧
      ChartGeometry.ofChart P = (views a).geometry k j ∧
      ChartFloors (views a).suffixChain k P (N final k ^ γ) E) ∧
    ∀ a g, (views a).suffixChain.selectedWorldLaw k E g = 0 ∨
      ENNReal.ofReal ((N final k ^ γ)⁻¹) ≤
        (views a).suffixChain.selectedWorldLaw k E g univ

theorem eventually_exists_flooredCore (views : α → OriginalView root final D S₀ η)
    (hz : Exact final) {p : Code} (common : RefinementChain p final)
    (hR : ∀ a k, (views a).suffixChain.referenceFactor k ≤ common.referenceFactor k)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent)
    (hε : ∀ a, 0 < ε a) (hu : ∀ a, 0 < u a) (huU : ∀ a, u a ≤ U (views a).parent)
    (hεsmall : ∀ a, ε a ≤ S (views a).parent * u a / 4) (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ k in atTop, ∃ E, FlooredCoreProperties views ε u tests γ k E := by
  classical
  have hcharts : ∀ᶠ k in atTop, ∀ a j, ∃ P : (views a).ChartAt (ε a) k j,
      (views a).chartChoice (ε a) j k = some P ∧
      ChartGeometry.ofChart P = (views a).geometry k j ∧
      ∀ ρ : Measure (Fin (W final k) × State), ρ ≪ worldMixture final k →
        ∀ᵐ z ∂ρ.map ((views a).suffixChain.pullback k), z ∈ IntermediateLiftSupport.chartRegion P := by
    apply Filter.eventually_all.2
    intro a
    exact (views a).eventually_chartChoice (ε a) (hε a)
  filter_upwards [hcharts, eventually_core_mass_half views hz ε u tests hε hu huU hεsmall,
    RootPacketFamilies.eventually_floorPruningLoss_small common hz
      (Fintype.card (CommonFloorIndex views)) γ hγ] with k hcharts hhalf hloss
  let Q : (a : α) → (j : Fin (views a).count) → (views a).ChartAt (ε a) k j :=
    fun a j => Classical.choose (hcharts a j)
  obtain ⟨E, hE, hEA, hmass, hfloor, hworld⟩ := exists_common_quarter_core views hz ε k Q
    (common.referenceFactor k) (N final k ^ γ)
    (Real.rpow_pos_of_pos (by linarith [hz.1.1 k]) _) (fun a => hR a k)
    (core views ε u tests k) (measurableSet_core views ε u tests k) hhalf hloss
  refine ⟨E, hE, hEA, hmass, ?_, hworld⟩
  intro a j
  exact ⟨Q a j, (Classical.choose_spec (hcharts a j)).1,
    (Classical.choose_spec (hcharts a j)).2.1, hfloor a j⟩

def flooredCore (views : α → OriginalView root final D S₀ η)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent) (γ : ℝ) (k : ℕ) :
    Set (Fin (W final k) × State) := by
  classical
  exact if h : ∃ E, FlooredCoreProperties views ε u tests γ k E
    then Classical.choose h else ∅

theorem measurableSet_flooredCore (views : α → OriginalView root final D S₀ η)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent) (γ : ℝ) (k : ℕ) :
    MeasurableSet (flooredCore views ε u tests γ k) := by
  classical
  unfold flooredCore
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact MeasurableSet.empty

theorem flooredCore_subset_core (views : α → OriginalView root final D S₀ η)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent) (γ : ℝ) (k : ℕ) :
    flooredCore views ε u tests γ k ⊆ core views ε u tests k := by
  classical
  unfold flooredCore
  split_ifs with h
  · exact (Classical.choose_spec h).2.1
  · exact empty_subset _

theorem eventually_flooredCore_properties (views : α → OriginalView root final D S₀ η)
    (hz : Exact final) {p : Code} (common : RefinementChain p final)
    (hR : ∀ a k, (views a).suffixChain.referenceFactor k ≤ common.referenceFactor k)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent)
    (hε : ∀ a, 0 < ε a) (hu : ∀ a, 0 < u a) (huU : ∀ a, u a ≤ U (views a).parent)
    (hεsmall : ∀ a, ε a ≤ S (views a).parent * u a / 4) (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ k in atTop, FlooredCoreProperties views ε u tests γ k
      (flooredCore views ε u tests γ k) := by
  classical
  filter_upwards [eventually_exists_flooredCore views hz common hR ε u tests
    hε hu huU hεsmall γ hγ] with k hk
  unfold flooredCore
  rw [dite_eq_left hk]
  exact Classical.choose_spec hk

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PreparedViews
