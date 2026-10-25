-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.ConditionedLikelihood, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/ConditionedLikelihood.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/ConditionedLikelihood.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/ConditionedLikelihood.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/ConditionedLikelihood.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.LikelihoodCut

/-! A global likelihood window gives a local joint cap under each ORIGINAL
coarse posterior, without changing the reference denominator after thinning. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Obl.k4_matching_cofinal_palette_selection

theorem cond_real_apply {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Set Ω) (hC : MeasurableSet C) (B : Set Ω) :
    (ProbabilityTheory.cond μ C).real B = μ.real (C ∩ B) / μ.real C := by
  simp only [measureReal_def, ProbabilityTheory.cond_apply hC, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

/-- The original coarse posterior sees the retained fine-history / velocity
joint cap against its OWN original marginals. No retained marginal is used. -/
theorem likelihoodGood_conditional_joint_cap {Ω Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) (hS : MeasurableSet S)
    (F : ℕ → Ω → ℕ) (z : Ω → Z) (start stop : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hstart : Measurable (F start))
    (hnest : ∀ x ∈ S, ∀ y ∈ S, F stop x = F stop y → F start x = F start y)
    (c e : ℕ) (a : Z) :
    (ProbabilityTheory.cond μ (S ∩ {x | F start x = c})).real
      {x | x ∈ likelihoodGood μ S F z start stop R ∧ F stop x = e ∧ z x = a} ≤
      R * (ProbabilityTheory.cond μ (S ∩ {x | F start x = c})).real {x | F stop x = e} *
        (ProbabilityTheory.cond μ (S ∩ {x | F start x = c})).real {x | z x = a} := by
  let C := S ∩ {x | F start x = c}
  let A := {x | x ∈ likelihoodGood μ S F z start stop R ∧ F stop x = e ∧ z x = a}
  have hC : MeasurableSet C := hS.inter (measurableSet_eq_fun hstart measurable_const)
  by_cases hne : (C ∩ A).Nonempty
  · obtain ⟨x₀, hxC, hxA⟩ := hne
    have hxS : x₀ ∈ S := hxC.1
    have hxc : F start x₀ = c := hxC.2
    have hxe : F stop x₀ = e := hxA.2.1
    have hxa : z x₀ = a := hxA.2.2
    have hFine : {x | x ∈ S ∧ F stop x = F stop x₀} = C ∩ {x | F stop x = e} := by
      ext x
      constructor
      · rintro ⟨hx, hf⟩
        exact ⟨⟨hx, (hnest x hx x₀ hxS hf).trans hxc⟩, hf.trans hxe⟩
      · rintro ⟨⟨hx, _⟩, hf⟩
        exact ⟨hx, hf.trans hxe.symm⟩
    have hJoint : {x | x ∈ likelihoodGood μ S F z start stop R ∧
        F stop x = F stop x₀ ∧ z x = z x₀} = C ∩ A := by
      ext x
      constructor
      · rintro ⟨hx, hf, hz⟩
        exact ⟨⟨hx.1, (hnest x hx.1 x₀ hxS hf).trans hxc⟩,
          hx, hf.trans hxe, hz.trans hxa⟩
      · rintro ⟨_, hx, hf, hz⟩
        exact ⟨hx, hf.trans hxe.symm, hz.trans hxa.symm⟩
    have hPalette : supportLikelihood μ S F z start x₀ =
        (ProbabilityTheory.cond μ C).real {x | z x = a} := by
      rw [cond_real_apply μ C hC]
      have heq : {x | x ∈ S ∧ F start x = F start x₀ ∧ z x = z x₀} =
          C ∩ {x | z x = a} := by
        ext x
        simp only [C, hxc, hxa, mem_inter_iff, mem_ofPred_eq]
        tauto
      have heqC : {x | x ∈ S ∧ F start x = F start x₀} = C := by
        ext x
        simp only [C, hxc, mem_inter_iff, mem_ofPred_eq]
      simp only [supportLikelihood, ← measureReal_def, heq, heqC]
    have hcap := likelihoodGood_joint_cap μ S F z start stop R hR hnest x₀ hxS
    rw [hJoint, hFine, hPalette] at hcap
    change (ProbabilityTheory.cond μ C).real A ≤ _
    rw [cond_real_apply μ C hC A, cond_real_apply μ C hC {x | F stop x = e}]
    calc
      _ ≤ (R * μ.real (C ∩ {x | F stop x = e}) *
          (ProbabilityTheory.cond μ C).real {x | z x = a}) / μ.real C := by
        exact div_le_div_of_nonneg_right hcap measureReal_nonneg
      _ = _ := by ring
  · have hempty : C ∩ A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change (ProbabilityTheory.cond μ C).real A ≤ _
    rw [cond_real_apply μ C hC A, hempty, measureReal_empty, zero_div]
    exact mul_nonneg (mul_nonneg hR measureReal_nonneg) measureReal_nonneg

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
