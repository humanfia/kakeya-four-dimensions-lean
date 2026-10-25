-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CanonicalParameterWorlds, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/CanonicalParameterWorlds.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/CanonicalParameterWorlds.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/CanonicalParameterWorlds.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicParameterBins
import Submission.Lib.K4ContinuousPlanks.Discretization

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set

noncomputable section

/-- The fixed original aligned coefficient-bin corner. -/
def parameterCenter (ρ : ℝ) (q : Fin 7 → ℤ) : Fin 7 → ℝ := fun i => ρ*(q i : ℝ)

theorem original_parameter_center_distance (ρ : ℝ) (hρ : 0 < ρ)
    (c : Fin 7 → ℝ) : ∀ i, |c i-parameterCenter ρ (parameterCode ρ c) i| ≤ ρ := by
  intro i
  have hlow := Int.floor_le (c i/ρ)
  have hhigh := Int.lt_floor_add_one (c i/ρ)
  have hlo := (le_div_iff₀ hρ).mp hlow
  have hhi := (div_lt_iff₀ hρ).mp hhigh
  change |c i-ρ*(⌊c i/ρ⌋ : ℝ)| ≤ ρ
  apply abs_le.mpr
  constructor <;> nlinarith

theorem original_parameter_center_bound (ρ K : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (c : Fin 7 → ℝ) (hc : ∀ i, |c i| ≤ K) :
    ∀ i, |parameterCenter ρ (parameterCode ρ c) i| ≤ K+1 := by
  intro i
  have hh := original_parameter_center_distance ρ hρ c i
  have hd := abs_sub_le (parameterCenter ρ (parameterCode ρ c) i) (c i) 0
  rw [sub_zero,sub_zero,abs_sub_comm _ (c i)] at hd
  linarith [hc i]

theorem original_parameter_zoom_coefficients_bound (ρ : ℝ) (hρ : 0 < ρ)
    (c : Fin 7 → ℝ) :
    ∀ i, |zoomCoefficients ρ (parameterCenter ρ (parameterCode ρ c)) c i| ≤ 1 := by
  intro i
  exact (norm_le_pi_norm (zoomCoefficients ρ (parameterCenter ρ (parameterCode ρ c)) c) i).trans
    (zoom_coefficients_bound ρ hρ _ _ (original_parameter_center_distance ρ hρ c))

/-- Actual original coefficient bounds give a finite full parameter-world
carrier without discretizing trajectories or discarding their tags. -/
theorem original_parameter_worlds_finite {Λ : Type*} (E : Set (Λ × ℝ))
    (c : Λ → Fin 7 → ℝ) (ρ K : ℝ) (hρ : 0 < ρ)
    (hc : ∀ z ∈ E, ∀ i, |c z.1 i| ≤ K) :
    ((fun z : Λ × ℝ => parameterCode ρ (c z.1)) '' E).Finite := by
  have hh := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
    (fun z : E => c z.val.1) K (fun z i => hc z.val z.property i) hρ
  have heq : Set.range (fun z : E => parameterCode ρ (c z.val.1)) =
      (fun z : Λ × ℝ => parameterCode ρ (c z.1)) '' E := by
    ext q
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z.val,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,rfl⟩
  rw [← heq]
  exact hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
