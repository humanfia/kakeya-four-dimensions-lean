-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.Jets2.ListedPalette, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/Jets2/ListedPalette.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 18a3db56eab47c441a364ba278c399c30491bda9,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/Jets2/ListedPalette.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.ParameterCompatibility
import Submission.Obl.k4_scalar_graph_residual_discovery.ParameterRefinement

/-! # Coarsen a fixed discrete palette using bounded compatible lists

All masses are the original fine palette weights. No posterior is
recomputed and no source is deleted to answer a coarser velocity test.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

def listedPalette {I J : Type*} [DecidableEq J]
    (menu : I → Finset J) (weight : I → ENNReal) (j : J) : ENNReal :=
  ∑' i, if j∈menu i then weight i else 0

theorem tsum_listedPalette_le {I J : Type*} [DecidableEq J]
    (menu : I → Finset J) (weight : I → ENNReal) (M : ENNReal)
    (hmenu : ∀ i, ((menu i).card:ENNReal) ≤ M) :
    (∑' j, listedPalette menu weight j) ≤ M*∑' i, weight i := by
  simpa only [listedPalette,ENNReal.tsum_prod'] using
    Submission.Obl.k4_scalar_graph_residual_discovery.listed_reference_sum_le menu weight M hmenu

theorem finite_sum_listedPalette_le {I J : Type*} [DecidableEq J]
    (menu : I → Finset J) (weight : I → ENNReal) (M : ENNReal)
    (hmenu : ∀ i, ((menu i).card:ENNReal) ≤ M) (F : Finset J) :
    (∑ j∈F, listedPalette menu weight j) ≤ M*∑' i, weight i :=
  (ENNReal.sum_le_tsum F).trans (tsum_listedPalette_le menu weight M hmenu)

/-- A common old per-state/fine-velocity numerator cap answers every
coarser query by summing only compatible original palette weights. -/
theorem listed_palette_state_cap {Ω Q I J : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
    [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (fine : Ω → I) (hfine : Measurable fine) (coarse : Ω → J) (hcoarse : Measurable coarse)
    (menu : I → Finset J) (hsupport : ∀ z, coarse z∈menu (fine z))
    (weight : I → ENNReal) (reference : Q → ENNReal) (C : ENNReal)
    (hcap : ∀ q i, μ {z | state z=q ∧ fine z=i} ≤ C*reference q*weight i)
    (q : Q) (j : J) :
    μ {z | state z=q ∧ coarse z=j} ≤ C*reference q*listedPalette menu weight j := by
  let E := {z | state z=q ∧ coarse z=j}
  have hE : MeasurableSet E :=
    (hstate (measurableSet_singleton q)).inter (hcoarse (measurableSet_singleton j))
  have hpart := Submission.Obl.k4_crop_angular_finite_tail.measure_eq_tsum_label μ hfine hE
  change μ E ≤ _
  rw [hpart]
  calc
    _ ≤ ∑' i, (C*reference q)*(if j∈menu i then weight i else 0) := by
      apply ENNReal.tsum_le_tsum
      intro i
      by_cases hi : j∈menu i
      · rw [ite_eq_left hi]
        apply (measure_mono ?_).trans (hcap q i)
        intro z hz
        exact ⟨hz.1.1,hz.2⟩
      · rw [ite_eq_right hi,mul_zero]
        have hempty : E∩fine ⁻¹' {i}=∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hh := hsupport z
          rw [hz.1.2,show fine z=i from hz.2] at hh
          exact hi hh
        rw [hempty,measure_empty]
    _ = _ := ENNReal.tsum_mul_left

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
