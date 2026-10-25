-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoarseSelectionMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoarseSelectionMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CoarseSelectionMass.lean.
All earlier source attributions below are retained. -/
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory

noncomputable section

/-- Coarse-cell selections sum against their unchanged earlier reference
law. There is no loss proportional to the number of selected cells. -/
theorem finite_partition_relative_selection {X I : Type*} [MeasurableSpace X]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ ρ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (state : X → I) (hstate : Measurable state) (C : Finset I)
    (hcover : ∀ᵐ x ∂μ, state x ∈ C)
    (selected : I → Set X) (hselected : ∀ q ∈ C, MeasurableSet (selected q))
    (hsubset : ∀ q ∈ C, selected q ⊆ state ⁻¹' {q})
    {ε fraction : ℝ} (hε : 0 ≤ ε)
    (hloss : ∀ q ∈ C, μ.real (state ⁻¹' {q}) ≤ μ.real (selected q) +
      ε * ρ.real (state ⁻¹' {q}) + fraction * μ.real (state ⁻¹' {q})) :
    MeasurableSet (⋃ q ∈ C, selected q) ∧
      μ.real univ ≤ μ.real (⋃ q ∈ C, selected q) + ε * ρ.real univ + fraction * μ.real univ := by
  classical
  have hcell (q : I) : MeasurableSet (state ⁻¹' {q}) := hstate (measurableSet_singleton q)
  have hdisj : PairwiseDisjoint (↑C) (fun q => state ⁻¹' {q}) := by
    intro q hq r hr hqr
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hqr (hx.symm.trans hy)
  have hselDisj : PairwiseDisjoint (↑C) selected := by
    intro q hq r hr hqr
    exact (hdisj hq hr hqr).mono (hsubset q hq) (hsubset r hr)
  have hfull : μ (state ⁻¹' (C : Set I)) = μ univ := by
    have hh := congrArg (fun ν : Measure X => ν univ)
      (Measure.restrict_eq_self_of_ae_mem hcover)
    change (μ.restrict (state ⁻¹' (C : Set I))) univ = μ univ at hh
    rwa [Measure.restrict_apply_univ] at hh
  have hμsum : (∑ q ∈ C, μ.real (state ⁻¹' {q})) = μ.real univ :=
    (sum_measureReal_preimage_singleton C (fun q _ => hcell q)).trans
      (congrArg ENNReal.toReal hfull)
  have hρsum : (∑ q ∈ C, ρ.real (state ⁻¹' {q})) ≤ ρ.real univ :=
    sum_measureReal_le_measureReal_univ (fun q _ => hcell q) hdisj
  have hselMass : μ.real (⋃ q ∈ C, selected q) = ∑ q ∈ C, μ.real (selected q) :=
    measureReal_biUnion_finset hselDisj hselected
  refine ⟨MeasurableSet.biUnion C.countable_toSet hselected, ?_⟩
  calc
    μ.real univ = ∑ q ∈ C, μ.real (state ⁻¹' {q}) := hμsum.symm
    _ ≤ ∑ q ∈ C, (μ.real (selected q) + ε * ρ.real (state ⁻¹' {q}) +
        fraction * μ.real (state ⁻¹' {q})) := Finset.sum_le_sum hloss
    _ = μ.real (⋃ q ∈ C, selected q) + ε * (∑ q ∈ C, ρ.real (state ⁻¹' {q})) +
        fraction * μ.real univ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hμsum, ← hselMass]
    _ ≤ μ.real (⋃ q ∈ C, selected q) + ε * ρ.real univ + fraction * μ.real univ := by
      gcongr

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
