import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewCharts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensityTests

/-! All candidate parents share one immutable mask for both original
width exclusions and every requested original density test. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PreparedViews

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open PathMeasures
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

variable {α : Type*} [Fintype α] {root final : Code} {D S₀ η : ℝ}

abbrev Index (views : α → OriginalView root final D S₀ η) :=
  ((a : α) × Fin (views a).count) ⊕ α

def parents (views : α → OriginalView root final D S₀ η) : Index views → Code
  | .inl i => (views i.1).parent
  | .inr a => (views a).parent

def chains (views : α → OriginalView root final D S₀ η) :
    (i : Index views) → RefinementChain (parents views i) final
  | .inl i => (views i.1).suffixChain
  | .inr a => (views a).suffixChain

def bad (views : α → OriginalView root final D S₀ η) (ε u : α → ℝ)
    (tests : (a : α) → DensityTests (views a).parent) (i : Index views) (k : ℕ) :
    Set (Fin (W (parents views i) ((chains views i).sample k)) × State) :=
  match i with
  | .inl i => taggedEvent
      (WidthGeometry.narrowEvent ((views i.1).layerAt (ε i.1) i.2 k) (ε i.1) (u i.1))
  | .inr a => (tests a).bad ((views a).suffixChain.sample k)

def core (views : α → OriginalView root final D S₀ η) (ε u : α → ℝ)
    (tests : (a : α) → DensityTests (views a).parent) (k : ℕ) :
    Set (Fin (W final k) × State) :=
  viewsMask (parents views) (chains views) (bad views ε u tests) k

theorem measurableSet_bad (views : α → OriginalView root final D S₀ η) (ε u : α → ℝ)
    (tests : (a : α) → DensityTests (views a).parent) (i : Index views) (k : ℕ) :
    MeasurableSet (bad views ε u tests i k) := by
  cases i with
  | inl i => exact (views i.1).measurableSet_narrowTagged (ε i.1) (u i.1) i.2 k
  | inr a => exact (tests a).measurableSet_bad (views a).parent_exact _

theorem measurableSet_core (views : α → OriginalView root final D S₀ η) (ε u : α → ℝ)
    (tests : (a : α) → DensityTests (views a).parent) (k : ℕ) :
    MeasurableSet (core views ε u tests k) :=
  measurableSet_viewsMask _ _ _ (measurableSet_bad views ε u tests) k

/-- The fixed finite menus are removed before any window is selected. -/
theorem eventually_core_mass_half (views : α → OriginalView root final D S₀ η)
    (hz : Exact final) (ε u : α → ℝ)
    (tests : (a : α) → DensityTests (views a).parent)
    (hε : ∀ a, 0 < ε a) (hu : ∀ a, 0 < u a) (huU : ∀ a, u a ≤ U (views a).parent)
    (hεsmall : ∀ a, ε a ≤ S (views a).parent * u a / 4) :
    ∀ᶠ k in atTop, ENNReal.ofReal (1 / 2 : ℝ) ≤
      normalizedWorldMixture final k (core views ε u tests k) := by
  apply eventually_viewsMask_mass_half (parents views) (chains views) (bad views ε u tests) hz
    (measurableSet_bad views ε u tests)
  intro i
  cases i with
  | inl i =>
    exact (views i.1).narrowTagged_powerSmall (ε i.1) (u i.1)
      (hε i.1) (hu i.1) (huU i.1) (hεsmall i.1) i.2
  | inr a =>
    obtain ⟨c, hc, hb⟩ := (tests a).bad_powerSmall (views a).parent_exact
    refine ⟨c, hc, ?_⟩
    filter_upwards [(views a).suffixChain.sample_strictMono.tendsto_atTop.eventually hb]
      with k hk
    rw [(views a).suffixChain.resolution k]
    exact hk

theorem preimage_null (views : α → OriginalView root final D S₀ η) (ε u : α → ℝ)
    (tests : (a : α) → DensityTests (views a).parent) (k : ℕ)
    (ρ : Measure (Fin (W final k) × State))
    (hρ : ρ ≤ (normalizedWorldMixture final k).restrict (core views ε u tests k))
    (i : Index views) : ρ ((chains views i).pullback k ⁻¹' bad views ε u tests i k) = 0 := by
  have hn := restrict_viewsMask_null (parents views) (chains views) (bad views ε u tests)
    (measurableSet_bad views ε u tests) i k
  exact le_antisymm ((hρ _).trans_eq hn) zero_le

/-- Width support persists under every later dominated common residual. -/
theorem current_narrow_null (views : α → OriginalView root final D S₀ η) (ε u : α → ℝ)
    (tests : (a : α) → DensityTests (views a).parent) (k : ℕ)
    (ρ : Measure (Fin (W final k) × State))
    (hρ : ρ ≤ (normalizedWorldMixture final k).restrict (core views ε u tests k))
    (a : α) (j : Fin (views a).count) (g : Fin (W (views a).parent ((views a).suffixChain.sample k))) :
    (views a).suffixChain.submeasureWorldLaw k ρ g
      (WidthGeometry.narrowEvent ((views a).layerAt (ε a) j k) (ε a) (u a) g) = 0 := by
  apply (views a).suffixChain.submeasureWorldLaw_null k _
    ((views a).measurableSet_narrow (ε a) (u a) j k)
  exact preimage_null views ε u tests k ρ hρ (.inl ⟨a, j⟩)

/-- Every requested original pure cap remains available for all later
laws, including the one used for the information-window argument. -/
theorem current_pure_null (views : α → OriginalView root final D S₀ η) (ε u : α → ℝ)
    (tests : (a : α) → DensityTests (views a).parent) (k : ℕ)
    (ρ : Measure (Fin (W final k) × State))
    (hρ : ρ ≤ (normalizedWorldMixture final k).restrict (core views ε u tests k))
    (a : α) (r : ℝ) (hr : r ∈ (tests a).pure)
    (g : Fin (W (views a).parent ((views a).suffixChain.sample k))) :
    (views a).suffixChain.submeasureWorldLaw k ρ g
      (pureException (views a).parent ((views a).suffixChain.sample k) g r (tests a).tolerance) = 0 := by
  have hv := (tests a).pure_valid r hr
  apply (views a).suffixChain.submeasureWorldLaw_null k _
    (fun g => measurableSet_pureException (views a).parent_exact _ g hv.1 hv.2 _)
  apply measure_mono_null (preimage_mono ((tests a).pure_subset_bad _ r hr))
  exact preimage_null views ε u tests k ρ hρ (.inr a)

theorem current_angular_null (views : α → OriginalView root final D S₀ η) (ε u : α → ℝ)
    (tests : (a : α) → DensityTests (views a).parent) (k : ℕ)
    (ρ : Measure (Fin (W final k) × State))
    (hρ : ρ ≤ (normalizedWorldMixture final k).restrict (core views ε u tests k))
    (a : α) (b : ℝ) (hb : b ∈ (tests a).angular)
    (g : Fin (W (views a).parent ((views a).suffixChain.sample k))) :
    (views a).suffixChain.submeasureWorldLaw k ρ g
      (angularException (views a).parent ((views a).suffixChain.sample k) g b (tests a).tolerance) = 0 := by
  have hv := (tests a).angular_valid b hb
  apply (views a).suffixChain.submeasureWorldLaw_null k _
    (fun g => measurableSet_angularException (views a).parent_exact _ g hv.1 hv.2 _)
  apply measure_mono_null (preimage_mono ((tests a).angular_subset_bad _ b hb))
  exact preimage_null views ε u tests k ρ hρ (.inr a)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PreparedViews
