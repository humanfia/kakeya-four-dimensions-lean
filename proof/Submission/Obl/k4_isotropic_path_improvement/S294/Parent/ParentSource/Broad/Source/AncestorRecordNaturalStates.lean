-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorRecordNaturalStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RecordNaturalStates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorRecordQueries

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
open scoped ENNReal

noncomputable section

/-- The actual fixed ancestor records construct natural states refining
BOTH a graph query and a later physical query. Both81-option menus are
derived from true chart differences. One6561-option fraction restriction
passes the palette and breadth together, while the graph readout stays
exact and the state remains globally faithful off the retained source. -/
theorem ancestor_record_query_natural_states
    {W : ℕ} {p : PathData W} {Rec : Type*}
    [Fintype Rec] [MeasurableSpace Rec] [MeasurableSingletonClass Rec]
    (N : ℝ) (root first second : Fin p.C)
    (piece : Rec → Set Ev) (code : Rec → Fin 4 → ℤ)
    (hm : ∀ r, MeasurableSet (piece r))
    (hdj : Pairwise (fun r s => Disjoint (piece r) (piece s)))
    (μ : Measure Ev) (hcoverage : ∀ᵐ z ∂μ, ∃ r, z∈piece r)
    {baseRef hiddenRef base₁ hidden₁ base₂ hidden₂ : ℝ}
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef)
    (hbase₁ : 0 < base₁) (hhidden₁ : 0 < hidden₁)
    (hbase₂ : 0 < base₂) (hhidden₂ : 0 < hidden₂)
    (hrecords : ∀ r z, z∈piece r →
      (fun j => ⌊parentUnshearedCoordinates N p root (p.R root) z j /
        ((Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef : Fin 4 → ℝ) j)⌋)∈
      referenceCellOptions
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef)
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef) (code r))
    (hbaseBudget₁ : 3*((2:ℝ)^p.T (p.lev first)/(2:ℝ)^p.T (p.lev root))*baseRef ≤ base₁)
    (hhiddenBudget₁ : 3*(δ N (p.r (p.lev root))/δ N (p.r (p.lev first)))*hiddenRef ≤ hidden₁)
    (hbaseBudget₂ : 3*((2:ℝ)^p.T (p.lev second)/(2:ℝ)^p.T (p.lev root))*baseRef ≤ base₂)
    (hhiddenBudget₂ : 3*(δ N (p.r (p.lev root))/δ N (p.r (p.lev second)))*hiddenRef ≤ hidden₂)
    (S : Set Ev) (hS : MeasurableSet S) (hcoverS : ∀ z∈S, ∃ r, z∈piece r)
    (beta : ENNReal) (hbeta : beta≠0) (hbetaTop : beta≠⊤)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) {bound : ℝ} (hbound : 0 ≤ bound)
    (hrow : ∀ q j, |row q j| ≤ bound) :
    let firstCode := fun z => jointCode base₁ hidden₁
      (fun j => unshearedPacketBase p first z j) (physicalParentSignal N p first (p.R root) z);
    let secondCode := fun z => jointCode base₂ hidden₂
      (fun j => unshearedPacketBase p second z j) (physicalParentSignal N p second (p.R root) z);
    ∃ (keep : Set Ev) (state : Ev → ℕ) (value : ℕ → Fin 3 → ℝ),
      MeasurableSet keep ∧ keep⊆S ∧ Measurable state ∧ (state '' keep).Finite ∧
      μ (S\keep) ≤ (6561:ENNReal)*beta*μ univ ∧
      (∀ x y, state x=state y → firstCode x=firstCode y ∧ secondCode x=secondCode y) ∧
      (∀ z, value (state z)=row (firstCode z)) ∧
      (∀ n j, |value n j| ≤ bound) ∧
      (∀ (B : Set Ev) (cap : ENNReal),
        (∀ r, μ (piece r∩B) ≤ cap*μ (piece r)) →
        (∀ q, μ ((keep∩firstCode ⁻¹' {q})∩B) ≤ (cap/beta)*μ (keep∩firstCode ⁻¹' {q})) ∧
        ∀ q, μ ((keep∩secondCode ⁻¹' {q})∩B) ≤ (cap/beta)*μ (keep∩secondCode ⁻¹' {q})) ∧
      ∀ (B : Set Ev) (cap : ENNReal),
        (∀ r, μ (piece r∩B) ≤ cap*μ (piece r)) →
        ∀ n, μ ((keep∩state ⁻¹' {n})∩B) ≤ (cap/beta)*μ (keep∩state ⁻¹' {n}) := by
  intro firstCode secondCode
  classical
  obtain ⟨options₁,hcard₁,hcover₁,_hpadding₁⟩ := ancestor_record_query_menus N root first piece code
    hbaseRef hhiddenRef hbase₁ hhidden₁ hrecords hbaseBudget₁ hhiddenBudget₁
  obtain ⟨options₂,hcard₂,hcover₂,_hpadding₂⟩ := ancestor_record_query_menus N root second piece code
    hbaseRef hhiddenRef hbase₂ hhidden₂ hrecords hbaseBudget₂ hhiddenBudget₂
  have measurableCode (child : Fin p.C) (base hidden : ℝ) :
      Measurable (fun z => jointCode base hidden (fun j => unshearedPacketBase p child z j)
        (physicalParentSignal N p child (p.R root) z)) := by
    have heq : (fun z => jointCode base hidden (fun j => unshearedPacketBase p child z j)
        (physicalParentSignal N p child (p.R root) z))=
        fun z j => ⌊parentUnshearedCoordinates N p child (p.R root) z j /
          ((Fin.snoc (fun _ : Fin 3 => base) hidden : Fin 4 → ℝ) j)⌋ :=
      funext (ancestor_joint_code_eq_coordinate_floors N base hidden p root child)
    rw [heq]
    apply measurable_pi_iff.mpr
    intro j
    exact Int.measurable_floor.comp (((measurable_pi_apply j).comp
      (measurable_parentUnshearedCoordinates N p child (p.R root))).div_const _)
  let pairCode := fun z : Ev => (firstCode z,secondCode z)
  let menus := fun r => (options₁ r).product (options₂ r)
  have hcard (r : Rec) : (menus r).card ≤ 6561 := by
    calc
      _ = (options₁ r).card*(options₂ r).card := Finset.card_product _ _
      _ ≤ 81*81 := Nat.mul_le_mul (hcard₁ r) (hcard₂ r)
      _ = _ := by norm_num
  have hoptions : ∀ r, ∀ z∈S∩piece r, pairCode z∈menus r := by
    intro r z hz
    apply Finset.mem_product.mpr
    constructor
    · simpa only [pairCode,firstCode,ancestor_joint_code_eq_coordinate_floors] using hcover₁ r z hz.2
    · simpa only [pairCode,secondCode,ancestor_joint_code_eq_coordinate_floors] using hcover₂ r z hz.2
  obtain ⟨keep,state,value,hkeep,hsub,hstate,hfinite,hloss,hfaith,hvalue,hbound',hcodeRatios,hratios⟩ :=
    exists_record_refined_natural_states μ piece hm hdj hcoverage pairCode
      ((measurableCode first base₁ hidden₁).prodMk (measurableCode second base₂ hidden₂))
      S hS hcoverS menus 6561 hcard hoptions beta hbeta hbetaTop
      (fun q => row q.1) hbound (fun q j => hrow q.1 j)
  refine ⟨keep,state,value,hkeep,hsub,hstate,hfinite,hloss,?_,hvalue,hbound',?_,hratios⟩
  · intro x y hxy
    exact Prod.mk.inj (hfaith x y hxy)
  · intro B cap hcap
    have hpaired (q₁ q₂ : Fin 4 → ℤ) :
        μ ((keep∩{z | firstCode z=q₁ ∧ secondCode z=q₂})∩B) ≤
          (cap/beta)*μ (keep∩{z | firstCode z=q₁ ∧ secondCode z=q₂}) := by
      have heq : pairCode ⁻¹' {(q₁,q₂)}={z | firstCode z=q₁ ∧ secondCode z=q₂} := by
        ext z
        simp only [mem_preimage,mem_singleton_iff,mem_ofPred_eq,pairCode,Prod.mk.injEq]
      simpa only [heq] using hcodeRatios B cap hcap (q₁,q₂)
    constructor
    · apply countable_joined_ratios_forget_record μ secondCode
        (measurableCode second base₂ hidden₂) firstCode (measurableCode first base₁ hidden₁)
        keep hkeep B (cap/beta)
      intro q₂ q₁
      simpa only [and_comm] using hpaired q₁ q₂
    · exact countable_joined_ratios_forget_record μ firstCode
        (measurableCode first base₁ hidden₁) secondCode (measurableCode second base₂ hidden₂)
        keep hkeep B (cap/beta) hpaired

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
