-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Search, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Search.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Search.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Search.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Caps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockMass
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAnchorOverlap

set_option autoImplicit false

/-!
# Choosing the anchor and the sliced group of a block (version 2)

The `j = 2` counterpart of `exists_original_block_search` of o078 (session x0662, branch `x0662`
at `f2bac599`, `ScalarBlockSearch.lean`): in a time block `[s, s + H]` of labelled mass at least
`H/K`, an anchor time `c = s + H · anchor` (paper: `u_*`, by Cauchy–Schwarz) and one sliced
starting group at `c` (scalar `H`-bin and `p`-slice of `y_{k'}(c)`) whose normalized prior has
total mass at most `250000 K⁶` and whose centered event has mass at least
`K⁻² / (250000 K⁶)` under (time law of the block) × (normalized group prior).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

theorem exists_v2_block_search {ν : Measure Λ} [IsProbabilityMeasure ν] {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {K ζ d H p s : ℝ} (h : UpperHyp ν c E F K ζ d)
    (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hd : d ≤ 1) (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H)
    (hHp : H ≤ p) (hp1 : p ≤ 1) (k : Fin 2)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) (hmass : H / K ≤ (ν.prod volume).real E) :
    ∃ (anchor : ℝ) (b : ℤ × ℤ), anchor ∈ Icc (0 : ℝ) 1 ∧ s + H * anchor ∈ activeTimes E ∧
      (slicedPrior ν c F E (s + H * anchor) H p d k b).real univ ≤ 250000 * K ^ 6 ∧
      (K⁻¹) ^ 2 / (250000 * K ^ 6) ≤
        ((scalarIntervalTime (-anchor)).prod (slicedPrior ν c F E (s + H * anchor) H p d k b)).real
          (scalarCenteredEvent E (slicedLabels c F E (s + H * anchor) H p k b) (s + H * anchor) H) := by
  let μ := scalarUnitTime
  letI : IsProbabilityMeasure μ := scalarUnitTime_probability
  let E₀ := scalarCenteredEvent E univ s H
  have hE₀ : MeasurableSet E₀ :=
    scalarCenteredEvent_measurable h.event_measurable MeasurableSet.univ s H
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hmass₀ : K⁻¹ ≤ (μ.prod ν).real E₀ := by
    have hm : (μ.prod ν).real E₀ = (ν.prod volume).real E / H := by
      simpa only [μ, E₀, mul_zero, add_zero, neg_zero, scalarIntervalTime,
        scalarUnitTime, zero_add, univ_prod_univ, inter_univ] using
        original_centered_event_real ν h.event_measurable MeasurableSet.univ s 0 hH hblock
    rw [hm]
    apply (le_div_iff₀ hH).mpr
    simpa only [div_eq_mul_inv, mul_comm] using hmass
  have hnull : μ (Icc (0 : ℝ) 1)ᶜ = 0 := by simp [μ, scalarUnitTime]
  obtain ⟨anchor, hanchor, hoverlap⟩ := exists_original_anchor_event μ ν hE₀ hnull
  have ha : anchor ∈ Icc (0 : ℝ) 1 := by
    simpa only [mem_compl_iff, not_not] using hanchor
  set t₀ := s + H * anchor with ht₀
  let A₀ : Set Λ := (fun l => (l, t₀)) ⁻¹' E
  let P := E₀ ∩ (univ ×ˢ A₀)
  have hA₀ : MeasurableSet A₀ := measurable_prodMk_right h.event_measurable
  have hP : MeasurableSet P := hE₀.inter (MeasurableSet.univ.prod hA₀)
  have hsection : Prod.mk anchor ⁻¹' E₀ = A₀ := by
    ext l
    simp [E₀, A₀, t₀, scalarCenteredEvent, scalarCenteredLift]
  have hδ : 0 < (K⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.mpr hKpos)
  have hPmass : (K⁻¹) ^ 2 ≤ (μ.prod ν).real P := by
    rw [hsection, show ν.real univ = 1 from by simp [Measure.real]] at hoverlap
    have hsq : (K⁻¹) ^ 2 ≤ ((μ.prod ν).real E₀) ^ 2 :=
      (sq_le_sq₀ (inv_nonneg.mpr hKpos.le) measureReal_nonneg).mpr hmass₀
    simpa only [one_mul] using hsq.trans hoverlap
  have hPne : P.Nonempty := by
    by_contra hne
    have he : P = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [he, measureReal_empty] at hPmass
    exact (not_le_of_gt hδ) hPmass
  have hc : t₀ ∈ activeTimes E := by
    obtain ⟨q, hq⟩ := hPne
    exact ⟨q.2, hq.2.2⟩
  obtain ⟨b, hprior, hselected⟩ := exists_sliced_starting_group h hK hd0 hd hH hH1 hζH hHp hp1
    t₀ k μ hP (fun q hq => hq.2) hδ hPmass
  have hselected_set : P ∩ (univ ×ˢ {l | slicedCode c F t₀ H p k l = b}) =
      scalarCenteredEvent E (slicedLabels c F E t₀ H p k b) s H := by
    ext q
    simp only [P, E₀, A₀, scalarCenteredEvent, slicedLabels, mem_inter_iff, mem_preimage,
      mem_prod, mem_univ, mem_setOf_eq, true_and, and_true]
    tauto
  rw [hselected_set] at hselected
  refine ⟨anchor, b, ha, hc, hprior, ?_⟩
  haveI := slicedPrior_finite ν c F E t₀ H p d k b
  rw [original_recentered_event_real (slicedPrior ν c F E t₀ H p d k b) h.event_measurable
    (slicedLabels_measurable h.measurable_c h.event_measurable F t₀ H p k b) s anchor hH hblock]
  exact hselected

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
