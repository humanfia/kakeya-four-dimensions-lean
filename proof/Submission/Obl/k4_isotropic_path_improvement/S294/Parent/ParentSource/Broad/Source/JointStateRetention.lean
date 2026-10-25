-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.JointStateRetention, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/JointStateRetention.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_physical_parent_potential_candidates.InterceptState

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory
open Submission.Lib.K4StateFractionKeep
open scoped ENNReal

noncomputable section

/-- Join a second state label after bounded-ambiguity fraction pruning.
The ORIGINAL law pays only M*beta, regardless of the number of either
kind of state. EVERY original conditional ratio passes to each joined
state with the single factor beta^-1. The accepted fraction-keep and
finite-menu charging theorems supply all the measure estimates. -/
theorem bounded_menu_joint_state_retention
    {Ω I J : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
    (μ : Measure Ω) (state : Ω → I) (hstate : Measurable state)
    (group : Ω → J) (hgroup : Measurable group)
    (S : Set Ω) (hS : MeasurableSet S)
    (menu : I → Finset J) (M : ℕ) (hM : ∀ i, (menu i).card ≤ M)
    (hmenu : ∀ x∈S, group x∈menu (state x))
    (beta : ENNReal) (hbeta : beta≠0) (hbetaTop : beta≠∞) :
    ∃ keep : Set Ω, MeasurableSet keep ∧ keep⊆S ∧
      μ (S\keep) ≤ (M : ENNReal)*beta*μ univ ∧
      ∀ (B : Set Ω) (cap : ENNReal),
        (∀ i, μ (state ⁻¹' {i}∩B) ≤ cap*μ (state ⁻¹' {i})) →
        ∀ i j,
          μ ((keep∩{x | state x=i ∧ group x=j})∩B) ≤
            (cap/beta)*μ (keep∩{x | state x=i ∧ group x=j}) := by
  classical
  let groupSet := fun j : J => S∩group ⁻¹' {j}
  let kept := fun j : J => fractionKeep μ state (groupSet j) beta
  let keep := ⋃ j : J, kept j
  have hkept (j : J) : MeasurableSet (kept j) :=
    measurableSet_fractionKeep hstate (hS.inter (hgroup (measurableSet_singleton j))) beta
  have hkeep : MeasurableSet keep := MeasurableSet.iUnion hkept
  have hsub : keep⊆S := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    exact hj.1.1
  have hcharge (j : J) : μ (groupSet j\kept j) ≤ beta*μ {x | j∈menu (state x)} := by
    apply (measure_diff_fractionKeep_le μ hstate (groupSet j) beta).trans
    apply mul_le_mul' le_rfl (measure_mono _)
    rintro x ⟨y,hy,hys⟩
    have hyj : group y=j := hy.2
    have hys' : state y=state x := hys
    have hh := hmenu y hy.1
    rwa [hyj,hys'] at hh
  have hsum : (∑' j : J, μ {x | j∈menu (state x)}) ≤ (M : ENNReal)*μ univ := by
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    exact Submission.Obl.k4_physical_parent_potential_candidates.finite_menu_overlap_sum_le
      μ state hstate menu M hM F
  have hcover : S\keep⊆⋃ j : J, groupSet j\kept j := by
    intro x hx
    refine mem_iUnion.mpr ⟨group x,⟨hx.1,rfl⟩,?_⟩
    intro hk
    exact hx.2 (mem_iUnion.mpr ⟨group x,hk⟩)
  have hcost : μ (S\keep) ≤ (M : ENNReal)*beta*μ univ := by
    calc
      _ ≤ μ (⋃ j : J, groupSet j\kept j) := measure_mono hcover
      _ ≤ ∑' j : J, μ (groupSet j\kept j) := measure_iUnion_le _
      _ ≤ ∑' j : J, beta*μ {x | j∈menu (state x)} := ENNReal.tsum_le_tsum hcharge
      _ = beta*(∑' j : J, μ {x | j∈menu (state x)}) := ENNReal.tsum_mul_left
      _ ≤ beta*((M : ENNReal)*μ univ) := mul_le_mul' le_rfl hsum
      _ = _ := by ac_rfl
  have hcell (i : I) (j : J) :
      keep∩{x | state x=i ∧ group x=j}=kept j∩state ⁻¹' {i} := by
    ext x
    constructor
    · rintro ⟨hx,hi,hj⟩
      obtain ⟨g,hg⟩ := mem_iUnion.mp hx
      have hgj : g=j := (show group x=g from hg.1.2).symm.trans hj
      subst g
      exact ⟨hg,hi⟩
    · rintro ⟨hx,hi⟩
      exact ⟨mem_iUnion.mpr ⟨j,hx⟩,hi,hx.1.2⟩
  refine ⟨keep,hkeep,hsub,hcost,?_⟩
  intro B cap hcap i j
  rw [hcell i j]
  exact fractionKeep_state_ratio μ state (groupSet j) hbeta hbetaTop B cap hcap i

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
