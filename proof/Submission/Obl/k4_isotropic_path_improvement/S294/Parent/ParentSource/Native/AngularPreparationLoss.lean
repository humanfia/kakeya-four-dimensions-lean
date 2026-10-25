-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.AngularPreparationLoss, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/AngularPreparationLoss.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/AngularPreparationLoss.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/AngularPreparationLoss.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.AngularResidual
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.OriginalDeletion

/-! Keep the actual omission budget when the fixed parent angular masks
are imposed. This permits a buffered original mass floor. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

theorem assemble_weighted_angular_preparation_loss {Γ Ω X P T I : Type*}
    [Fintype Γ] [Fintype P] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Γ → Measure Ω) (weight : Γ → ENNReal) (H : Γ → Set Ω)
    (E : Γ → P → Set Ω) (obs : Γ → Ω → X) (ang : Γ → T → Ω → I)
    (hH : ∀ w, MeasurableSet (H w)) (hE : ∀ w b, MeasurableSet (E w b))
    (hobs : ∀ w, Measurable (obs w)) (loss : ENNReal) (cap : Γ → T → ENNReal)
    (hbudget : ∑ w, weight w * μ w univ ≤ 1)
    (hprepared : ∀ w, ∃ A : P → Set X, (∀ b, MeasurableSet (A b)) ∧
      (∑ b, (μ w).restrict (E w b) {p | obs w p ∉ A b}) ≤ loss * μ w univ ∧
      ∀ t b i, maskedParentLaw (μ w) (E w) (obs w) A b {p | ang w t p = i} ≤
        cap w t * maskedParentLaw (μ w) (E w) (obs w) A b univ) :
    ∃ A : Γ → P → Set X, (∀ w b, MeasurableSet (A w b)) ∧
      (∀ w, MeasurableSet (observationFamilyCut (H w) (E w) (obs w) (A w))) ∧
      (∀ w, observationFamilyCut (H w) (E w) (obs w) (A w) ⊆ H w) ∧
      (∑ w, weight w * μ w (H w)) ≤
        (∑ w, weight w * μ w (observationFamilyCut (H w) (E w) (obs w) (A w))) + loss ∧
      (∀ w b, (μ w).restrict
        (observationFamilyCut (H w) (E w) (obs w) (A w) ∩ E w b) ≤
          maskedParentLaw (μ w) (E w) (obs w) (A w) b) ∧
      ∀ w t b i, maskedParentLaw (μ w) (E w) (obs w) (A w) b {p | ang w t p = i} ≤
        cap w t * maskedParentLaw (μ w) (E w) (obs w) (A w) b univ := by
  classical
  choose A hA hloss hcap using hprepared
  let S := fun w => observationFamilyCut (H w) (E w) (obs w) (A w)
  have hS (w : Γ) : S w ⊆ H w := sdiff_subset
  have hbad : (∑ w, weight w * μ w (H w \ S w)) ≤ loss := by
    calc
      _ ≤ ∑ w, weight w * (loss * μ w univ) := by
        apply Finset.sum_le_sum
        intro w _
        exact mul_le_mul_of_nonneg_left
          ((observationFamilyCut_omission_le (μ w) (H w) (E w) (obs w) (A w)
            (hobs w) (hA w)).trans (hloss w)) zero_le
      _ = loss * ∑ w, weight w * μ w univ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ ≤ loss * 1 := mul_le_mul_of_nonneg_left hbudget zero_le
      _ = loss := mul_one _
  have heq (w : Γ) : H w \ (H w \ S w) = S w := by
    ext x
    constructor
    · intro hx
      by_contra hn
      exact hx.2 ⟨hx.1, hn⟩
    · intro hx
      exact ⟨hS w hx, fun h => h.2 hx⟩
  refine ⟨A, hA, fun w => measurableSet_observationFamilyCut (hH w) (hE w) (hobs w) (hA w),
    hS, ?_, ?_, hcap⟩
  · have h := (mixture_le_sdiff_add μ weight H (fun w => H w \ S w)).trans
      (add_le_add le_rfl hbad)
    simpa only [heq] using h
  · intro w b
    exact observationFamilyCut_parent_domination (μ w) (H w) (E w) (obs w) (A w)
      (hobs w) (hA w) b

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
