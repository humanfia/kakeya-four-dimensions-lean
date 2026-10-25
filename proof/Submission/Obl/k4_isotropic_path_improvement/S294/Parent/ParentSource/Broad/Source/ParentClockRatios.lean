-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentClockRatios, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentClockRatios.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentClockRatios.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalClockGridSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentStateBreadth

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

noncomputable section

/-- Physical parent-state ratios renewed after other source cuts pass
to the chosen clock grid under that same law. This uses only the exact
dyadic code map; no mass floor or further pruning is required. -/
theorem parent_clock_band_ratio {W : ℕ} (N : ℝ) (p : PathData W) (old : Fin p.C)
    (P : Po) (μ : Measure Ev) {ε : ℝ} (hε : 0 < ε) (steps : ℕ)
    (hbound : δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) ≤ (2:ℝ)^steps)
    (band : Set Ev) (hband : MeasurableSet band) (fraction : ENNReal)
    (hcap : ∀ q, μ ((gridCode (fun z j => unshearedPacketBase p old z j)
      (physicalParentSignal N p old P) ε ε) ⁻¹' {q}∩band) ≤
        fraction*μ ((gridCode (fun z j => unshearedPacketBase p old z j)
          (physicalParentSignal N p old P) ε ε) ⁻¹' {q})) :
    ∀ q, μ (clockParentCode p old P (ε*(2:ℝ)^steps) ⁻¹' {q}∩band) ≤
      fraction*μ (clockParentCode p old P (ε*(2:ℝ)^steps) ⁻¹' {q}) := by
  let base := fun z j => unshearedPacketBase p old z j
  let fine := gridCode base (physicalParentSignal N p old P) ε ε
  let clock := gridCode base (clockParentSignal p old P) (ε*(2:ℝ)^steps) (ε*(2:ℝ)^steps)
  have hbase : Measurable base := by
    apply measurable_pi_iff.mpr
    intro j
    exact (PiLp.continuous_apply 2 _ j).measurable.comp (measurable_unshearedPacketBase p old)
  have hfine : Measurable fine := ClockCalibration.measurable_product_gridCode base hbase
    _ (measurable_physicalParentSignal _ _ _ _) ε ε
  obtain ⟨heightSteps,hfactor⟩ := parent_clock_state_coarsening N p old P hε steps hbound
  let coarsen := coarsenProductGrid steps heightSteps
  have hfactor' (z : Ev) : clock z=coarsen (fine z) := hfactor z
  intro q
  rw [clockParentCode_fibre]
  have hset : clock ⁻¹' {splitClockCode q}∩band=
      {z | coarsen (fine z)=splitClockCode q ∧ z∈band} := by
    ext z
    change (clock z=splitClockCode q ∧ z∈band) ↔ _
    rw [hfactor']
    rfl
  have hset' : clock ⁻¹' {splitClockCode q}=
      {z | coarsen (fine z)=splitClockCode q} := by
    ext z
    change (clock z=splitClockCode q) ↔ _
    rw [hfactor']
    rfl
  change μ (clock ⁻¹' {splitClockCode q}∩band) ≤ fraction*μ (clock ⁻¹' {splitClockCode q})
  rw [hset,hset']
  exact state_ratio_under_map μ fine hfine coarsen band hband fraction hcap (splitClockCode q)

/-- The literal four-coordinate parent states supplied by actual
history breadth renewal give the same clock ratios. -/
theorem parent_clock_band_ratio_of_joint_state {W : ℕ}
    (N : ℝ) (p : PathData W) (old : Fin p.C) (P : Po) (μ : Measure Ev)
    {ε : ℝ} (hε : 0 < ε) (steps : ℕ)
    (hbound : δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) ≤ (2:ℝ)^steps)
    (band : Set Ev) (hband : MeasurableSet band) (fraction : ENNReal)
    (hcap : ∀ q : Fin 4 → ℤ,
      μ {z | jointCode ε ε (fun j => unshearedPacketBase p old z j)
          (physicalParentSignal N p old P z)=q ∧ z∈band} ≤
        fraction*μ {z | jointCode ε ε (fun j => unshearedPacketBase p old z j)
          (physicalParentSignal N p old P z)=q}) :
    ∀ q, μ (clockParentCode p old P (ε*(2:ℝ)^steps) ⁻¹' {q}∩band) ≤
      fraction*μ (clockParentCode p old P (ε*(2:ℝ)^steps) ⁻¹' {q}) := by
  let fine := gridCode (fun z j => unshearedPacketBase p old z j)
    (physicalParentSignal N p old P) ε ε
  let fine₄ := fun z => jointCode ε ε (fun j => unshearedPacketBase p old z j)
    (physicalParentSignal N p old P z)
  have heq (z : Ev) : fine₄ z=flattenClockCode (fine z) := by
    ext j
    fin_cases j <;> rfl
  have hfibre (q : (Fin 3 → ℤ) × ℤ) :
      fine ⁻¹' {q}=fine₄ ⁻¹' {flattenClockCode q} := by
    ext z
    change (fine z=q)↔(fine₄ z=flattenClockCode q)
    rw [heq]
    exact flattenClockCode_injective.eq_iff.symm
  apply parent_clock_band_ratio N p old P μ hε steps hbound band hband fraction
  intro q
  change μ (fine ⁻¹' {q}∩band) ≤ fraction*μ (fine ⁻¹' {q})
  rw [hfibre]
  exact hcap (flattenClockCode q)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
