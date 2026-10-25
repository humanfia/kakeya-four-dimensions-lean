-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.CoarsePaletteTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/CoarsePaletteTransfer.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/CoarsePaletteTransfer.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/CoarsePaletteTransfer.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/CoarsePaletteTransfer.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.ConditionedLikelihood
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FinitePaletteSupport

/-! Combine the original-law likelihood window and the actual normalized
palette cut under one fixed coarse posterior. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set

def coarsePaletteCut {Ω Z Y : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (z : Ω → Z) (y : Ω → Y)
    (start stop c : ℕ) (R ε : ℝ) : Set Ω :=
  paletteStateCut (ProbabilityTheory.cond μ (S ∩ {x | F start x = c}))
    (likelihoodGood μ S F z start stop R ∩ (S ∩ {x | F start x = c})) z y ε

/-- Actual normalized-palette transfer inside one ORIGINAL coarse posterior.
Both marginal factors on the right are fixed before either omission. -/
theorem likelihood_coarse_palette_transfer {Ω Z Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [Countable Z] [MeasurableSingletonClass Z]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) (hS : MeasurableSet S)
    (F : ℕ → Ω → ℕ) (z : Ω → Z) (y : Ω → Y) (start stop c : ℕ)
    (hstart : Measurable (F start)) (hstop : Measurable (F stop))
    (hz : Measurable z) (hy : Measurable y)
    (hnest : ∀ x ∈ S, ∀ x' ∈ S, F stop x = F stop x' → F start x = F start x')
    (hCpos : μ (S ∩ {x | F start x = c}) ≠ 0)
    (hffin : (F stop '' (S ∩ {x | F start x = c})).Finite)
    (hzfin : (z '' (S ∩ {x | F start x = c})).Finite)
    (hyfin : (y '' (S ∩ {x | F start x = c})).Finite)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (K : ℕ)
    (hK : ∀ a, (y '' {x | x ∈ S ∩ {x | F start x = c} ∧ z x = a}).ncard ≤ K) :
    MeasurableSet (coarsePaletteCut μ S F z y start stop c R ε) ∧
      coarsePaletteCut μ S F z y start stop c R ε ⊆
        likelihoodGood μ S F z start stop R ∩ (S ∩ {x | F start x = c}) ∧
      (ProbabilityTheory.cond μ (S ∩ {x | F start x = c})).real
        ((likelihoodGood μ S F z start stop R ∩ (S ∩ {x | F start x = c})) \
          coarsePaletteCut μ S F z y start stop c R ε) ≤ ε * (K : ℝ) ∧
      ∀ e b, (ProbabilityTheory.cond μ (S ∩ {x | F start x = c})).real
        {x | x ∈ coarsePaletteCut μ S F z y start stop c R ε ∧ F stop x = e ∧ y x = b} ≤
          (R / ε) * (ProbabilityTheory.cond μ (S ∩ {x | F start x = c})).real {x | F stop x = e} *
            (ProbabilityTheory.cond μ (S ∩ {x | F start x = c})).real {x | y x = b} := by
  let C := S ∩ {x | F start x = c}
  let π := ProbabilityTheory.cond μ C
  have hC : MeasurableSet C := hS.inter (measurableSet_eq_fun hstart measurable_const)
  let := ProbabilityTheory.cond_isProbabilityMeasure (μ := μ) hCpos
  have hπC : π Cᶜ = 0 := ae_iff.mp (ProbabilityTheory.ae_cond_mem (μ := μ) hC)
  have hG : MeasurableSet (likelihoodGood μ S F z start stop R) :=
    measurableSet_likelihoodGood μ S F z start stop R hS hstart hstop hz
  have hOld (e : ℕ) (a : Z) : π.real
      {x | x ∈ likelihoodGood μ S F z start stop R ∩ C ∧ F stop x = e ∧ z x = a} ≤
      R * π.real {x | F stop x = e} * π.real {x | z x = a} := by
    have hle : π.real
        {x | x ∈ likelihoodGood μ S F z start stop R ∩ C ∧ F stop x = e ∧ z x = a} ≤
        π.real {x | x ∈ likelihoodGood μ S F z start stop R ∧ F stop x = e ∧ z x = a} :=
      measureReal_mono (fun x hx => ⟨hx.1.1, hx.2⟩)
    exact hle.trans (likelihoodGood_conditional_joint_cap μ S hS F z start stop R hR hstart hnest c e a)
  exact continuous_palette_refinement_on_support π C
    (likelihoodGood μ S F z start stop R ∩ C) hC hπC (hG.inter hC) inter_subset_right
    (F stop) z y hstop hz hy hffin hzfin hyfin hε hR K hK hOld

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
