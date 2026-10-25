import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathViews
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensityTests

/-! Finite candidate menus have one fixed original format budget.
Their original density menus can be extended by every actual layer depth. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set PathMeasures
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {root final : Code} {D₀ S₀ η : ℝ}

theorem exists_common_view_budget {α : Type*} [Fintype α]
    (views : α → OriginalView root final D₀ S₀ η) :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ a,
      (views a).complexity ≤ M₀ ∧ M (views a).parent ≤ M₀ ∧ D (views a).parent ≤ M₀ ∧
        L (views a).parent ≤ (M₀ : ℝ) := by
  classical
  let F : α → ℕ := fun a => max (views a).complexity
    (max (M (views a).parent) (max (D (views a).parent) ⌈L (views a).parent⌉₊))
  let M₀ := Finset.univ.sup F + 1
  have hF (a : α) : F a ≤ M₀ :=
    (Finset.le_sup (f := F) (Finset.mem_univ a)).trans (Nat.le_add_right _ _)
  refine ⟨M₀, by dsimp [M₀]; omega, ?_⟩
  intro a
  have hc : (views a).complexity ≤ M₀ := (le_max_left _ _).trans (hF a)
  have hM : M (views a).parent ≤ M₀ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hF a))
  have hD : D (views a).parent ≤ M₀ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hF a)))
  have hL : ⌈L (views a).parent⌉₊ ≤ M₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hF a)))
  exact ⟨hc, hM, hD, (Nat.le_ceil _).trans (by exact_mod_cast hL)⟩

def OriginalView.withLayerTests (a : OriginalView root final D₀ S₀ η)
    (t : DensityTests a.parent) : DensityTests a.parent where
  pure := t.pure ∪ Finset.univ.image a.depth
  angular := t.angular
  tolerance := t.tolerance
  tolerance_pos := t.tolerance_pos
  pure_valid := by
    intro r hr
    rcases Finset.mem_union.mp hr with ht | hl
    · exact t.pure_valid r ht
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
      exact ⟨(a.depth_bounds j).1, (a.depth_bounds j).2.le⟩
  angular_valid := t.angular_valid

theorem OriginalView.layer_mem_withLayerTests (a : OriginalView root final D₀ S₀ η)
    (t : DensityTests a.parent) (j : Fin a.count) : a.depth j ∈ (a.withLayerTests t).pure := by
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)

theorem OriginalView.pure_mem_withLayerTests (a : OriginalView root final D₀ S₀ η)
    (t : DensityTests a.parent) {r : ℝ} (hr : r ∈ t.pure) : r ∈ (a.withLayerTests t).pure :=
  Finset.mem_union_left _ hr

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
