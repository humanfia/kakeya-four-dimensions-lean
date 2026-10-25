-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalEntrySnapshots, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalEntrySnapshots.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Mathlib

/-! # Current entry floors bound original time fibers

A selected original coefficient atom has a lower bound in the current
incidence law. Summing these disjoint entries controls its full original
prior at any fixed time. The incidence duration cancels against the same
duration in a current cell ceiling. Priors are never replaced by the
selected incidence posterior.
-/

set_option autoImplicit false
namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
open Set MeasureTheory
open scoped ENNReal
noncomputable section

/-- Original bin floors on every selected atom bound the original
snapshot mass by the total current entry mass, without counting atoms. -/
theorem original_snapshot_mass_of_entry_floors
    {Λ Ω B : Type*} [MeasurableSpace Λ] [MeasurableSpace Ω]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B]
    (ν : Measure Λ) (μ : Measure Ω) (code : Λ → B) (hcode : Measurable code)
    (entryCode : Ω → B) (hentry : Measurable entryCode)
    (S : Set Λ) (rate : ℝ≥0∞)
    (hfloor : ∀ l∈S, rate*ν (code ⁻¹' {code l}) ≤
      μ (entryCode ⁻¹' {code l})) : rate*ν S ≤ μ univ := by
  have hsingle (b : B) : rate*(ν.restrict S) (code ⁻¹' {b}) ≤
      μ (entryCode ⁻¹' {b}) := by
    by_cases hb : ∃ l∈S, code l=b
    · obtain ⟨l,hl,rfl⟩ := hb
      exact (mul_le_mul' le_rfl (Measure.restrict_le_self _)).trans (hfloor l hl)
    · have hn : code ⁻¹' {b} ∩ S=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro l hl
        exact hb ⟨l,hl.2,hl.1⟩
      rw [Measure.restrict_apply (hcode (measurableSet_singleton b)),hn,measure_empty,mul_zero]
      exact bot_le
  have hν : (∑' b : (univ : Set B), (ν.restrict S) (code ⁻¹' {(b : B)}))=ν S := by
    simpa only [preimage_univ,Measure.restrict_apply_univ] using
      (tsum_measure_preimage_singleton (μ := ν.restrict S) (s := univ)
        (to_countable univ) (fun b _ => hcode (measurableSet_singleton b)))
  have hμ : (∑' b : (univ : Set B), μ (entryCode ⁻¹' {(b : B)}))=μ univ := by
    simpa only [preimage_univ] using
      (tsum_measure_preimage_singleton (μ := μ) (s := univ)
        (to_countable univ) (fun b _ => hentry (measurableSet_singleton b)))
  rw [←hν,←hμ,←ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (fun b => hsingle b)


/-- Entry floors give an original fixed-time cap in every canonical
cell, including any union of intrinsic trajectory bins. -/
theorem original_cell_snapshot_of_entry_floors
    {Λ B Q : Type*} [MeasurableSpace Λ]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (ν : Measure Λ) (μ : Measure (Λ×ℝ))
    (code : Λ → B) (hcode : Measurable code)
    (cell : Λ×ℝ → Q) (hcell : Measurable cell)
    (R : Set (Λ×ℝ)) (rate : ℝ≥0∞)
    (hfloor : ∀ z∈R, rate*ν (code ⁻¹' {code z.1}) ≤
      μ {w | code w.1=code z.1 ∧ cell w=cell z})
    (t : ℝ) (q : Q) (D : Set B) :
    rate*ν {l | (l,t)∈R ∧ cell (l,t)=q ∧ code l∈D} ≤
      μ {z | cell z=q ∧ code z.1∈D} := by
  let U : Set (Λ×ℝ) := {z | cell z=q ∧ code z.1∈D}
  have hm : MeasurableSet U :=
    (hcell (measurableSet_singleton q)).inter
      ((hcode.comp measurable_fst) (to_countable D).measurableSet)
  have hentry : Measurable (fun z : Λ×ℝ => code z.1) := hcode.comp measurable_fst
  have h := original_snapshot_mass_of_entry_floors ν (μ.restrict U) code hcode
    (fun z : Λ×ℝ => code z.1) hentry
    {l | (l,t)∈R ∧ cell (l,t)=q ∧ code l∈D} rate ?_
  · simpa only [Measure.restrict_apply_univ] using h
  · rintro l ⟨hl,hq,hD⟩
    refine (hfloor (l,t) hl).trans_eq ?_
    rw [Measure.restrict_apply (hentry (measurableSet_singleton (code l)))]
    congr 1
    ext z
    simp only [mem_ofPred_eq,mem_inter_iff,mem_preimage,mem_singleton_iff,U]
    constructor
    · rintro ⟨hcodez,hcellz⟩
      exact ⟨hcodez,hcellz.trans hq,by simpa only [hcodez] using hD⟩
    · rintro ⟨hcodez,hcellz,_⟩
      exact ⟨hcodez,hcellz.trans hq.symm⟩

/-- The matching incidence duration cancels from the original snapshot
ceiling. No reciprocal scale enters the resulting constant. -/
theorem original_cell_snapshot_cap
    {Λ B Q : Type*} [MeasurableSpace Λ]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (ν : Measure Λ) (μ : Measure (Λ×ℝ))
    (code : Λ → B) (hcode : Measurable code)
    (cell : Λ×ℝ → Q) (hcell : Measurable cell)
    (R : Set (Λ×ℝ)) {cut s C amplitude : ℝ}
    (hcut : 0 < cut) (hs : 0 < s)
    (hfloor : ∀ z∈R, ENNReal.ofReal (cut*s)*ν (code ⁻¹' {code z.1}) ≤
      μ {w | code w.1=code z.1 ∧ cell w=cell z})
    (t : ℝ) (q : Q) (D : Set B) (weight : ℝ≥0∞)
    (hcap : μ {z | cell z=q ∧ code z.1∈D} ≤
      ENNReal.ofReal (C*s*amplitude)*weight) :
    ν {l | (l,t)∈R ∧ cell (l,t)=q ∧ code l∈D} ≤
      ENNReal.ofReal (C*amplitude/cut)*weight := by
  have hmass := (original_cell_snapshot_of_entry_floors ν μ code hcode cell hcell R
    (ENNReal.ofReal (cut*s)) hfloor t q D).trans hcap
  have hrate : 0 < cut*s := mul_pos hcut hs
  have hdiv : ν {l | (l,t)∈R ∧ cell (l,t)=q ∧ code l∈D} ≤
      (ENNReal.ofReal (C*s*amplitude)*weight)/ENNReal.ofReal (cut*s) := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hrate))) (Or.inl ENNReal.ofReal_ne_top)).mpr
    simpa only [mul_comm] using hmass
  refine hdiv.trans_eq ?_
  calc
    _ = (ENNReal.ofReal (C*s*amplitude)/ENNReal.ofReal (cut*s))*weight := by
      simp only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
    _ = ENNReal.ofReal (C*amplitude/cut)*weight := by
      rw [←ENNReal.ofReal_div_of_pos hrate]
      congr 2
      field_simp

/-- The original snapshot can test any union of full current entries.
The coefficient atom may meet many cells; the pairs are disjoint. -/
theorem original_union_snapshot_of_entry_floors
    {Λ B Q : Type*} [MeasurableSpace Λ]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (ν : Measure Λ) (μ : Measure (Λ×ℝ))
    (code : Λ → B) (hcode : Measurable code)
    (cell : Λ×ℝ → Q) (hcell : Measurable cell)
    (R : Set (Λ×ℝ)) (rate : ℝ≥0∞)
    (hfloor : ∀ z∈R, rate*ν (code ⁻¹' {code z.1}) ≤
      μ {w | code w.1=code z.1 ∧ cell w=cell z})
    (t : ℝ) (D : Set (B×Q)) :
    rate*ν {l | (l,t)∈R ∧ (code l,cell (l,t))∈D} ≤
      μ {z | (code z.1,cell z)∈D} := by
  let entry : Λ×ℝ → B×Q := fun z => (code z.1,cell z)
  let snapshot : Λ → B×Q := fun l => (code l,cell (l,t))
  let U : Set (Λ×ℝ) := {z | entry z∈D}
  have hentry : Measurable entry := (hcode.comp measurable_fst).prodMk hcell
  have hsnapshot : Measurable snapshot := hcode.prodMk
    (hcell.comp (measurable_id.prodMk measurable_const))
  have hU : MeasurableSet U := hentry (to_countable D).measurableSet
  have h := original_snapshot_mass_of_entry_floors ν (μ.restrict U)
    snapshot hsnapshot entry hentry {l | (l,t)∈R ∧ snapshot l∈D} rate ?_
  · simpa only [Measure.restrict_apply_univ] using h
  · rintro l ⟨hl,hD⟩
    have hsub : snapshot ⁻¹' {snapshot l} ⊆ code ⁻¹' {code l} := by
      intro l' hl'
      exact congrArg Prod.fst hl'
    refine (mul_le_mul' le_rfl (measure_mono hsub)).trans
      ((hfloor (l,t) hl).trans_eq ?_)
    rw [Measure.restrict_apply (hentry (measurableSet_singleton _))]
    congr 1
    ext z
    simp only [mem_ofPred_eq,mem_inter_iff,mem_preimage,mem_singleton_iff,U,entry,snapshot]
    constructor
    · rintro ⟨hcodez,hcellz⟩
      have heq : (code z.1,cell z)=(code l,cell (l,t)) := Prod.ext hcodez hcellz
      exact ⟨heq,heq.symm ▸ hD⟩
    · rintro ⟨heq,_⟩
      exact ⟨congrArg Prod.fst heq,congrArg Prod.snd heq⟩

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
