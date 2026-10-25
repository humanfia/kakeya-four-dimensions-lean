-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.MovingBandCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/MovingBandCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/MovingBandCaps.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourcePhysicalCap
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- A constant-center hidden-band cap holds for any measurable center
that depends on the base point. The accepted measurable-label cap sums
the disjoint base regions without a range or derivative cost. -/
theorem moving_band_base_cap {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) (reference : Measure Y) (base : Ω → Y) (hbase : Measurable base)
    (signal : Ω → ℝ) (center : Y → ℝ) (hcenter : Measurable center)
    {width : ℝ} (hwidth : 0 < width) (C : ENNReal)
    (hcap : ∀ a : ℝ, (μ.restrict {z | |signal z-a| ≤ 2*width}).map base ≤ C • reference) :
    (μ.restrict {z | |signal z-center (base z)| ≤ width}).map base ≤ C • reference := by
  let selected := μ.restrict {z | |signal z-center (base z)| ≤ width}
  let label : Ω → ℤ := fun z => ⌊center (base z)/width⌋
  let baseLabel : Y → ℤ := fun y => ⌊center y/width⌋
  have hlabels (n : ℤ) : MeasurableSet {y | baseLabel y=n} :=
    measurableSet_eq_fun (hcenter.div_const width).floor measurable_const
  have hfixed (n : ℤ) (E : Set Y) (hE : MeasurableSet E) :
      selected {z | base z ∈ E ∧ label z=n} ≤ C*reference E := by
    have hset : MeasurableSet {z | base z ∈ E ∧ label z=n} :=
      (hE.preimage hbase).inter ((hlabels n).preimage hbase)
    have hh := hcap (width*(n:ℝ)) E
    rw [Measure.map_apply hbase hE,Measure.restrict_apply (hE.preimage hbase),
      Measure.smul_apply,smul_eq_mul] at hh
    rw [Measure.restrict_apply hset]
    apply (measure_mono ?_).trans hh
    intro z hz
    refine ⟨hz.1.1,?_⟩
    have herr : |center (base z)-width*(n:ℝ)| ≤ width :=
      physical_grid_corner_error hwidth hz.1.2
    calc
      _ ≤ |signal z-center (base z)|+|center (base z)-width*(n:ℝ)| := abs_sub_le _ _ _
      _ ≤ width+width := add_le_add hz.2 herr
      _ = _ := by ring
  apply Measure.le_iff.mpr
  intro E hE
  have hh := Submission.Obl.k4_fixed_budget_quadratic_recovery.moving_label_cap
    selected reference base label C hfixed baseLabel hlabels E hE
  rw [Measure.map_apply hbase hE,Measure.smul_apply,smul_eq_mul]
  change selected {z | base z ∈ E} ≤ C*reference E
  simpa only [label,baseLabel,eq_self,and_true] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
