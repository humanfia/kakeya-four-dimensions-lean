-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PreparedPosteriors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PreparedPosteriors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PreparedPosteriors.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PreparedPosteriors.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/PreparedPosteriors.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PreparedLaw

/-! Conditioning the single prepared labelled law on one old world event
recovers exactly the native original-law posterior. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

theorem cond_smul_eq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {c : ENNReal} (hc : c ≠ 0) (hctop : c ≠ ∞) (S : Set X) :
    ProbabilityTheory.cond (c • μ) S = ProbabilityTheory.cond μ S := by
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul, Measure.restrict_smul,
    ENNReal.mul_inv (Or.inl hc) (Or.inl hctop), smul_smul]
  congr 1
  calc
    (c⁻¹ * (μ S)⁻¹) * c = (c⁻¹ * c) * (μ S)⁻¹ := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hc hctop, one_mul]

theorem map_cond_univ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (hf : Measurable f) :
    (ProbabilityTheory.cond μ univ).map f = ProbabilityTheory.cond (μ.map f) univ := by
  simp only [ProbabilityTheory.cond, Measure.restrict_univ,
    Measure.map_smul _ hf.aemeasurable]
  congr 1
  rw [Measure.map_apply hf MeasurableSet.univ]
  simp

theorem cond_restrict_univ {X : Type*} [MeasurableSpace X] (μ : Measure X) (S : Set X) :
    ProbabilityTheory.cond (μ.restrict S) univ = ProbabilityTheory.cond μ S := by
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.restrict_apply_univ]

/-- Restricting the labelled mixture to an event in one world leaves exactly
one original weighted component. -/
theorem labelledResidual_restrict_world {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X)
    (D : Set (Fin W × X)) (hD : MeasurableSet D) (w : Fin W)
    (hworld : ∀ z ∈ D, z.1 = w) :
    (labelledResidual μ ω H).restrict D = ENNReal.ofReal (ω w) •
      (μ w |>.restrict (H w ∩ {x | (w, x) ∈ D})).map (Prod.mk w) := by
  classical
  apply Measure.ext
  intro S hS
  rw [Measure.restrict_apply hS, labelledResidual_apply μ ω H _ (hS.inter hD),
    Measure.smul_apply, smul_eq_mul, Measure.map_apply measurable_prodMk_left hS,
    Measure.restrict_apply (hS.preimage measurable_prodMk_left)]
  calc
    _ = ENNReal.ofReal (ω w) * μ w (H w ∩ {x | (w, x) ∈ S ∩ D}) := by
      apply Finset.sum_eq_single w
      · intro a _ haw
        have he : H a ∩ {x | (a, x) ∈ S ∩ D} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact haw (hworld (a, x) hx.2.2)
        rw [he, measure_empty, mul_zero]
      · simp
    _ = _ := by
      congr 2
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
      tauto

/-- A prepared coarse posterior in one world is the native posterior under
the original measure. The global normalization and original world weight
cancel exactly; the event and all later references are unchanged. -/
theorem prepared_world_posterior {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X)
    (D : Set (Fin W × X)) (hD : MeasurableSet D) (w : Fin W)
    (hworld : ∀ z ∈ D, z.1 = w) (hω : 0 < ω w)
    (htotal : (labelledResidual μ ω H) univ ≠ ∞) :
    (ProbabilityTheory.cond (preparedResidualLaw μ ω H) D).map Prod.snd =
      ProbabilityTheory.cond (μ w) (H w ∩ {x | (w, x) ∈ D}) := by
  have hnorm : ProbabilityTheory.cond (preparedResidualLaw μ ω H) D =
      ProbabilityTheory.cond (labelledResidual μ ω H) D := by
    simpa only [preparedResidualLaw, univ_inter] using
      ProbabilityTheory.cond_cond_eq_cond_inter' MeasurableSet.univ hD htotal
  rw [hnorm, ← cond_restrict_univ, labelledResidual_restrict_world μ ω H D hD w hworld,
    cond_smul_eq _ (ENNReal.ofReal_ne_zero_iff.mpr hω) ENNReal.ofReal_ne_top,
    map_cond_univ _ Prod.snd measurable_snd,
    Measure.map_map measurable_snd measurable_prodMk_left]
  have hid : Prod.snd ∘ (Prod.mk w : X → Fin W × X) = id := rfl
  rw [hid, Measure.map_id, cond_restrict_univ]

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
