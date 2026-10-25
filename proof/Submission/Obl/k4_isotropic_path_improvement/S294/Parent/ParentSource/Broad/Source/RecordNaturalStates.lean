-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.RecordNaturalStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.JoinedNaturalStates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.JointStateRetention
import Submission.Obl.k4_wide_three_layer_scalar_inputs.FiniteLabels

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Forget a countable record label after uniform joined-state ratio
bounds. The query-code fibers inherit the identical ratio. -/
theorem countable_joined_ratios_forget_record
    {Ω I Code : Type*} [MeasurableSpace Ω]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace Code] [MeasurableSingletonClass Code]
    (μ : Measure Ω) (label : Ω → I) (hlabel : Measurable label)
    (code : Ω → Code) (hcode : Measurable code)
    (keep : Set Ω) (hkeep : MeasurableSet keep) (B : Set Ω) (cap : ENNReal)
    (hcap : ∀ i q, μ ((keep∩{z | label z=i ∧ code z=q})∩B) ≤
      cap*μ (keep∩{z | label z=i ∧ code z=q})) :
    ∀ q, μ ((keep∩code ⁻¹' {q})∩B) ≤ cap*μ (keep∩code ⁻¹' {q}) := by
  intro q
  let cells : I → Set Ω := fun i => keep∩{z | label z=i ∧ code z=q}
  have hm (i : I) : MeasurableSet (cells i) :=
    hkeep.inter ((hlabel (measurableSet_singleton i)).inter (hcode (measurableSet_singleton q)))
  have hdj : Pairwise (fun i j => Disjoint (cells i) (cells j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hij (hz.2.1.symm.trans hz'.2.1)
  have hset : keep∩code ⁻¹' {q}=⋃ i, cells i := by
    ext z
    simp only [cells,mem_inter_iff,mem_preimage,mem_singleton_iff,mem_iUnion,mem_setOf_eq]
    constructor
    · intro hz
      exact ⟨label z,hz.1,rfl,hz.2⟩
    · rintro ⟨i,hi,_,hq⟩
      exact ⟨hi,hq⟩
  have hinter : (⋃ i, cells i)∩B=⋃ i, cells i∩B := by
    ext z
    simp only [mem_inter_iff,mem_iUnion]
    constructor
    · rintro ⟨⟨i,hi⟩,hb⟩
      exact ⟨i,hi,hb⟩
    · rintro ⟨i,hi,hb⟩
      exact ⟨⟨i,hi⟩,hb⟩
  rw [hset,hinter]
  calc
    μ (⋃ i, cells i∩B) ≤ ∑' i, μ (cells i∩B) := measure_iUnion_le _
    _ ≤ ∑' i, cap*μ (cells i) := ENNReal.tsum_le_tsum (fun i => hcap i q)
    _ = cap*(∑' i, μ (cells i)) := ENNReal.tsum_mul_left
    _ = cap*μ (⋃ i, cells i) := congrArg (cap*·) (measure_iUnion hdj hm).symm

/-- Refine genuine finite records by actual queried codes, paying only
the bounded number of options per record. Natural state equality keeps
the queried code GLOBALLY, including off the selected source. The same
fraction pruning passes ALL current-record conditional event ratios,
so both the original palette and strip breadth survive together. -/
theorem exists_record_refined_natural_states
    {Ω Rec Code : Type*} [MeasurableSpace Ω]
    [Fintype Rec] [MeasurableSpace Rec] [MeasurableSingletonClass Rec]
    [MeasurableSpace Code] [Countable Code] [MeasurableSingletonClass Code]
    (μ : Measure Ω) (piece : Rec → Set Ω)
    (hm : ∀ r, MeasurableSet (piece r))
    (hdj : Pairwise (fun r s => Disjoint (piece r) (piece s)))
    (hcoverage : ∀ᵐ z ∂μ, ∃ r, z∈piece r)
    (code : Ω → Code) (hcode : Measurable code)
    (S : Set Ω) (hS : MeasurableSet S)
    (hcoverS : ∀ z∈S, ∃ r, z∈piece r)
    (menu : Rec → Finset Code) (M : ℕ) (hM : ∀ r, (menu r).card ≤ M)
    (hmenu : ∀ r, ∀ z∈S∩piece r, code z∈menu r)
    (beta : ENNReal) (hbeta : beta≠0) (hbetaTop : beta≠⊤)
    (row : Code → Fin 3 → ℝ) {bound : ℝ} (hbound : 0 ≤ bound)
    (hrow : ∀ q j, |row q j| ≤ bound) :
    ∃ (keep : Set Ω) (state : Ω → ℕ) (value : ℕ → Fin 3 → ℝ),
      MeasurableSet keep ∧ keep⊆S ∧ Measurable state ∧ (state '' keep).Finite ∧
      μ (S\keep) ≤ (M:ENNReal)*beta*μ univ ∧
      (∀ x y, state x=state y → code x=code y) ∧
      (∀ z, value (state z)=row (code z)) ∧
      (∀ n j, |value n j| ≤ bound) ∧
      (∀ (B : Set Ω) (cap : ENNReal),
        (∀ r, μ (piece r∩B) ≤ cap*μ (piece r)) →
        ∀ q, μ ((keep∩code ⁻¹' {q})∩B) ≤ (cap/beta)*μ (keep∩code ⁻¹' {q})) ∧
      ∀ (B : Set Ω) (cap : ENNReal),
        (∀ r, μ (piece r∩B) ≤ cap*μ (piece r)) →
        ∀ n, μ ((keep∩state ⁻¹' {n})∩B) ≤ (cap/beta)*μ (keep∩state ⁻¹' {n}) := by
  classical
  letI : MeasurableSpace (Option Rec) := ⊤
  letI : MeasurableSingletonClass (Option Rec) := ⟨fun _ => trivial⟩
  let pieces : Option Rec → Set Ω := fun r => r.elim ∅ piece
  have hpieces : ∀ r, MeasurableSet (pieces r) := by
    intro r
    cases r with
    | none => exact MeasurableSet.empty
    | some r => exact hm r
  have hdisj : ∀ r s : Option Rec, r≠s → Disjoint (pieces r) (pieces s) := by
    intro r s hrs
    cases r with
    | none => simp [pieces]
    | some r =>
      cases s with
      | none => simp [pieces]
      | some s => exact hdj (fun h => hrs (congrArg some h))
  obtain ⟨lab,hlabm,hlab,hdefault⟩ :=
    Submission.Obl.k4_wide_three_layer_scalar_inputs.exists_measurable_finite_label
      pieces hpieces hdisj none
  have hLab : Measurable lab := measurable_to_countable' hlabm
  have hSome (r : Rec) : lab ⁻¹' {some r}=piece r := by
    apply Set.Subset.antisymm
    · intro z hz
      have hz' : lab z=some r := hz
      by_cases he : ∃ s, z∈piece s
      · obtain ⟨s,hs⟩ := he
        have hs' : lab z=some s := hlab (some s) z hs
        have hsr : s=r := Option.some.inj (hs'.symm.trans hz')
        simpa only [hsr] using hs
      · have hmiss : ¬∃ s : Option Rec, z∈pieces s := by
          rintro ⟨s,hs⟩
          cases s with
          | none => exact hs
          | some s => exact he ⟨s,hs⟩
        cases (hz'.symm.trans (hdefault z hmiss))
    · intro z hz
      exact hlab (some r) z hz
  have hNone : μ (lab ⁻¹' {none})=0 := by
    apply measure_mono_null (t := {z | ¬∃ r, z∈piece r}) ?_ (ae_iff.mp hcoverage)
    intro z hz hmem
    obtain ⟨r,hr⟩ := hmem
    have hh : lab z=some r := hlab (some r) z hr
    cases ((show lab z=none from hz).symm.trans hh)
  let menus : Option Rec → Finset Code := fun r => r.elim ∅ menu
  have hMenus : ∀ r, (menus r).card ≤ M := by
    intro r
    cases r with
    | none => simp [menus]
    | some r => exact hM r
  have hOptions : ∀ z∈S, code z∈menus (lab z) := by
    intro z hz
    obtain ⟨r,hr⟩ := hcoverS z hz
    have hh : lab z=some r := hlab (some r) z hr
    simpa only [hh,menus,Option.elim_some] using hmenu r z ⟨hz,hr⟩
  obtain ⟨state,value,hstate,hfinite,hstateEq,hvalue,hrowBound⟩ :=
    exists_joined_natural_states lab hLab code hcode S (Set.toFinite _) menus hOptions
      row hbound hrow
  obtain ⟨keep,hkeep,hsub,hloss,hratios⟩ := bounded_menu_joint_state_retention
    μ lab hLab code hcode S hS menus M hMenus hOptions beta hbeta hbetaTop
  have liftCap (B : Set Ω) (cap : ENNReal)
      (hcap : ∀ r, μ (piece r∩B) ≤ cap*μ (piece r)) :
      ∀ r : Option Rec, μ (lab ⁻¹' {r}∩B) ≤ cap*μ (lab ⁻¹' {r}) := by
    intro r
    cases r with
    | none =>
      rw [hNone,mul_zero]
      exact (measure_mono inter_subset_left).trans_eq hNone
    | some r =>
      rw [hSome r]
      exact hcap r
  refine ⟨keep,state,value,hkeep,hsub,hstate,hfinite.subset (Set.image_mono hsub),hloss,
    (fun x y hxy => ((hstateEq x y).mp hxy).2),hvalue,hrowBound,?_,?_⟩
  · intro B cap hcap
    exact countable_joined_ratios_forget_record μ lab hLab code hcode keep hkeep B (cap/beta)
      (hratios B cap (liftCap B cap hcap))
  · intro B cap hcap
    exact joined_state_ratios_to_natural_codes μ state lab code hstateEq keep B (cap/beta)
      (hratios B cap (liftCap B cap hcap))

/-- Restricting to a region made of complete records preserves EVERY
current-record conditional ratio, with no deletion or extra factor. -/
theorem record_ratio_restrict_of_whole
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (piece region B : Set Ω) (hregion : MeasurableSet region)
    (hwhole : (piece∩region).Nonempty → piece⊆region) (cap : ENNReal)
    (hcap : μ (piece∩B) ≤ cap*μ piece) :
    (μ.restrict region) (piece∩B) ≤ cap*(μ.restrict region) piece := by
  by_cases h : (piece∩region).Nonempty
  · have hsub : piece⊆region := hwhole h
    rw [Measure.restrict_apply' hregion,Measure.restrict_apply' hregion,
      inter_eq_left.mpr (fun z hz => hsub hz.1),inter_eq_left.mpr hsub]
    exact hcap
  · have hz : (μ.restrict region) piece=0 := by
      rw [Measure.restrict_apply' hregion,Set.not_nonempty_iff_eq_empty.mp h,measure_empty]
    rw [hz,mul_zero]
    exact (measure_mono inter_subset_left).trans_eq hz

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
