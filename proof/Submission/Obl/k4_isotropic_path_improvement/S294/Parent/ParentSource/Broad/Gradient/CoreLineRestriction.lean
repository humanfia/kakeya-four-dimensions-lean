-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.CoreLineRestriction, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/CoreLineRestriction.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/CoreLineRestriction.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CoreGradientEntry

/-! # Whole original line restrictions commute with returning-row selection -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native

noncomputable section

theorem rowVolume_inter_lines (U : Set Event) (G : Set Line) (h : ℝ) (q : Event)
    (hq : q.1 ∈ G) :
    rowVolume (U ∩ Prod.fst ⁻¹' G) h q = rowVolume U h q := by
  unfold rowVolume
  congr 1
  ext t
  simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, hq, and_true]

theorem coreLongRows_inter_lines {W : ℕ} (p : Native.PathData W) (b : Fin p.C)
    (K : ℝ) (R : ℕ) (U : Set Event) (G : Set Line) (θ : ℝ) :
    coreLongRows p b K R (U ∩ Prod.fst ⁻¹' G) θ =
      coreLongRows p b K R U θ ∩ Prod.fst ⁻¹' G := by
  ext q
  by_cases hq : q.1 ∈ G
  · simp only [coreLongRows, mem_inter_iff, mem_setOf_eq, mem_preimage, hq, and_true,
      rowVolume_inter_lines U G _ q hq, true_and]
  · simp only [coreLongRows, mem_inter_iff, mem_setOf_eq, mem_preimage, hq, and_false,
      false_and]

theorem ae_prod_fst_mem {ν : Measure Line} {G : Set Line}
    (hG : MeasurableSet G) (hAE : ∀ᵐ l ∂ν, l ∈ G) :
    ∀ᵐ q ∂ν.prod (volume : Measure ℝ), q.1 ∈ G := by
  exact (Measure.ae_prod_iff_ae_ae (hG.preimage measurable_fst)).mpr
    (hAE.mono fun _ h => Filter.Eventually.of_forall fun _ => h)

theorem prod_restrict_inter_lines {ν : Measure Line} {G : Set Line}
    (hG : MeasurableSet G) (hAE : ∀ᵐ l ∂ν, l ∈ G) (U : Set Event) :
    (ν.prod volume).restrict (U ∩ Prod.fst ⁻¹' G) = (ν.prod volume).restrict U := by
  apply Measure.restrict_congr_set
  filter_upwards [ae_prod_fst_mem hG hAE] with q hq
  simp only [mem_inter_iff, mem_preimage, hq, and_true]

theorem ValueBranchData.entryLaw_inter_lines
    {d : ProblemData} {k : ℕ} {p : Native.PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) (b : Fin p.C) (a : Fin V.count)
    {G : Set Line} (hG : MeasurableSet G) (hAE : ∀ᵐ l ∂d.ν k (p.γ b), l ∈ G)
    (U : Set Event) :
    V.entryLaw b a (U ∩ Prod.fst ⁻¹' G) = V.entryLaw b a U := by
  simp only [ValueBranchData.entryLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (V.measurable b a).1]
  congr 1
  apply measure_congr
  filter_upwards [ae_prod_fst_mem hG hAE] with z hz
  simp only [mem_inter_iff, mem_preimage, hz, and_true]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
