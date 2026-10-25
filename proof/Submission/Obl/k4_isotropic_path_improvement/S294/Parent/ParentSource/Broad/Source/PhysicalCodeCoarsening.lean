-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.PhysicalCodeCoarsening, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/PhysicalCodeCoarsening.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/PhysicalCodeCoarsening.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalCodePruning
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CellBreadth
import Submission.Lib.K4XInterface.Basic

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory
open scoped ENNReal

noncomputable section

def coarsenPhysicalCode (baseSteps hiddenSteps : ℕ) (code : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun j => code j / (2 : ℤ) ^ (if j = 3 then hiddenSteps else baseSteps)

/-- Dyadic rectangular fine cells belong to one whole coarse cube. -/
theorem Native.PathData.originalPhysicalCode_coarsen {W : ℕ} (p : Native.PathData W)
    (Nk : ℝ) (old : Fin p.C) (baseMesh hidden coarse : ℝ) (baseSteps hiddenSteps : ℕ)
    (hbase : coarse = baseMesh * (2 : ℝ) ^ baseSteps)
    (hhidden : coarse = hidden * (2 : ℝ) ^ hiddenSteps) (z : Ev) :
    p.originalPhysicalCode Nk old coarse coarse z =
      coarsenPhysicalCode baseSteps hiddenSteps (p.originalPhysicalCode Nk old baseMesh hidden z) := by
  rw [p.originalPhysicalCode_isotropic, p.originalPhysicalCode_coordinates]
  funext j
  dsimp only [coarsenPhysicalCode]
  by_cases hj : j = 3
  · simp only [ite_eq_left hj]
    rw [hhidden, div_mul_eq_div_div, Submission.Lib.K4XInterface.floor_div_two_pow]
  · simp only [ite_eq_right hj]
    rw [hbase, div_mul_eq_div_div, Submission.Lib.K4XInterface.floor_div_two_pow]

/-- A restriction to a union of whole fine states preserves each individual
state law exactly, or deletes that whole law. -/
theorem restrict_fibre_under_coarsening {X I J : Type*} [MeasurableSpace X]
    [MeasurableSpace I] [MeasurableSingletonClass I] [DecidableEq J]
    (μ : Measure X) (fine : X → I) (hfine : Measurable fine) (coarsen : I → J)
    (q : J) (i : I) :
    (μ.restrict ((coarsen ∘ fine) ⁻¹' {q})).restrict (fine ⁻¹' {i}) =
      if coarsen i = q then μ.restrict (fine ⁻¹' {i}) else 0 := by
  classical
  rw [Measure.restrict_restrict (hfine (measurableSet_singleton i))]
  by_cases hi : coarsen i = q
  · rw [if_pos hi]
    congr 1
    apply inter_eq_left.mpr
    intro x hx
    change coarsen (fine x) = q
    rw [show fine x = i from hx, hi]
  · rw [if_neg hi]
    have he : fine ⁻¹' {i} ∩ (coarsen ∘ fine) ⁻¹' {q} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hi
      have hx1 : fine x = i := hx.1
      have hx2 : coarsen (fine x) = q := hx.2
      exact hx1 ▸ hx2
    rw [he, Measure.restrict_empty]

theorem Broad.Velocity.cellBroad_restrict_coarsening
    {X J : Type*} [MeasurableSpace X] {m d : ℕ}
    (μ : Measure X) (code : X → Fin m) (hcode : Measurable code)
    (coarsen : Fin m → J) (q : J) (e : X → EuclideanSpace ℝ (Fin d)) (ρ c : ℝ)
    (hbroad : ∀ i, cellBroad μ code e ρ c i) :
    ∀ i, cellBroad (μ.restrict ((coarsen ∘ code) ⁻¹' {q})) code e ρ c i := by
  classical
  intro i
  unfold cellBroad
  rw [restrict_fibre_under_coarsening μ code hcode coarsen q i]
  split_ifs with hi
  · exact hbroad i
  · simp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
