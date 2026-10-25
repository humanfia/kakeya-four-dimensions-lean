-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.AngularResidual, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/AngularResidual.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/AngularResidual.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/AngularResidual.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/AngularResidual.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.AngularPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Preparation

/-! All parent masks are assembled under the original weighted law before
the single probability normalization used by the later entropy argument. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable def maskedParentLaw {Ω X P : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : P → Set Ω) (obs : Ω → X) (A : P → Set X) (b : P) : Measure Ω :=
  (μ.restrict (E b)).restrict (obs ⁻¹' A b)

/-- The mask omission is paid once in the original world mixture. All parent
reference laws and their angular caps are retained after the global cut. -/
theorem assemble_weighted_angular_preparation {Γ Ω X P T I : Type*}
    [Fintype Γ] [Fintype P] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Γ → Measure Ω) (weight : Γ → ENNReal) (H : Γ → Set Ω)
    (E : Γ → P → Set Ω) (obs : Γ → Ω → X) (ang : Γ → T → Ω → I)
    (hH : ∀ w, MeasurableSet (H w)) (hE : ∀ w b, MeasurableSet (E w b))
    (hobs : ∀ w, Measurable (obs w)) (δ : ENNReal) (cap : Γ → T → ENNReal)
    (hbudget : ∑ w, weight w * μ w univ ≤ 1)
    (hprepared : ∀ w, ∃ A : P → Set X, (∀ b, MeasurableSet (A b)) ∧
      (∑ b, (μ w).restrict (E w b) {p | obs w p ∉ A b}) ≤ δ * μ w univ ∧
      ∀ t b i, maskedParentLaw (μ w) (E w) (obs w) A b {p | ang w t p = i} ≤
        cap w t * maskedParentLaw (μ w) (E w) (obs w) A b univ)
    {a : ℝ} (ha : 0 ≤ a) (hδ : δ ≤ ENNReal.ofReal (a / 2))
    (hmass : ENNReal.ofReal a ≤ ∑ w, weight w * μ w (H w)) :
    ∃ A : Γ → P → Set X, (∀ w b, MeasurableSet (A w b)) ∧
      (∀ w, MeasurableSet (observationFamilyCut (H w) (E w) (obs w) (A w))) ∧
      (∀ w, observationFamilyCut (H w) (E w) (obs w) (A w) ⊆ H w) ∧
      ENNReal.ofReal (a / 2) ≤
        ∑ w, weight w * μ w (observationFamilyCut (H w) (E w) (obs w) (A w)) ∧
      (∀ w b, (μ w).restrict
        (observationFamilyCut (H w) (E w) (obs w) (A w) ∩ E w b) ≤
          maskedParentLaw (μ w) (E w) (obs w) (A w) b) ∧
      ∀ w t b i, maskedParentLaw (μ w) (E w) (obs w) (A w) b {p | ang w t p = i} ≤
        cap w t * maskedParentLaw (μ w) (E w) (obs w) (A w) b univ := by
  classical
  choose A hA hloss hcap using hprepared
  let S : Γ → Set Ω := fun w => observationFamilyCut (H w) (E w) (obs w) (A w)
  have hS (w : Γ) : S w ⊆ H w := sdiff_subset
  have hbad : (∑ w, weight w * μ w (H w \ S w)) ≤ ENNReal.ofReal (a / 2) := by
    calc
      _ ≤ ∑ w, weight w * (δ * μ w univ) := by
        apply Finset.sum_le_sum
        intro w _
        exact mul_le_mul le_rfl ((observationFamilyCut_omission_le (μ w) (H w) (E w)
          (obs w) (A w) (hobs w) (hA w)).trans (hloss w)) zero_le zero_le
      _ = δ * ∑ w, weight w * μ w univ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ ≤ δ := by simpa only [mul_one] using mul_le_mul le_rfl hbudget zero_le zero_le
      _ ≤ _ := hδ
  have hkeep := mixture_remove_half μ weight H (fun w => H w \ S w) ha hmass hbad
  have heq (w : Γ) : H w \ (H w \ S w) = S w := by
    ext p
    constructor
    · intro hp
      by_contra hn
      exact hp.2 ⟨hp.1, hn⟩
    · intro hp
      exact ⟨hS w hp, fun hn => hn.2 hp⟩
  refine ⟨A, hA, ?_, hS, ?_, ?_, hcap⟩
  · intro w
    exact measurableSet_observationFamilyCut (hH w) (hE w) (hobs w) (hA w)
  · simpa only [heq] using hkeep
  · intro w b
    exact observationFamilyCut_parent_domination (μ w) (H w) (E w) (obs w) (A w)
      (hobs w) (hA w) b

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
