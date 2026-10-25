-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.HistoryMenuRecords, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/HistoryMenuRecords.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Lib.K4ListedExceptions.FrameCodes

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette

open Set MeasureTheory
open Submission.Lib.K4ListedExceptions

noncomputable section

/-- Enumerate the actual short state menus, then split each history into
its state fibers. The partition is fixed at this one reference grid,
before all later geometric queries. Its size is the PER-HISTORY menu size. -/
theorem exists_history_menu_records
    {Ω Index Code : Type*} [MeasurableSpace Ω] [MeasurableSpace Code]
    [MeasurableSingletonClass Code] [DecidableEq Code]
    (E : Set Ω) (hE : MeasurableSet E)
    (Hist : Index → Set Ω) (hHist : ∀ v, MeasurableSet (Hist v))
    (hHistDisj : Pairwise (fun v w => Disjoint (Hist v) (Hist w)))
    (state : Ω → Code) (hstate : Measurable state)
    (menus : Index → Finset Code)
    (hmenu : ∀ v, ∀ z∈E∩Hist v, state z∈menus v) :
    ∃ (n : Index → ℕ) (code : (v : Index) → Fin (n v) → Code)
      (piece : (Σ v, Fin (n v)) → Set Ω),
      (∀ v, n v=(menus v).card) ∧
      (∀ r, MeasurableSet (piece r)) ∧
      (∀ r, piece r ⊆ E∩Hist r.1) ∧
      Pairwise (fun r s => Disjoint (piece r) (piece s)) ∧
      (∀ r, ∀ z∈piece r, state z=code r.1 r.2) ∧
      ∀ z∈E, (∃ v, z∈Hist v) → ∃ r, z∈piece r := by
  classical
  let n : Index → ℕ := fun v => Fintype.card ↥(menus v)
  let code : (v : Index) → Fin (n v) → Code :=
    fun v j => ((Fintype.equivFin ↥(menus v)).symm j).1
  let piece : (Σ v, Fin (n v)) → Set Ω :=
    fun r => (E∩Hist r.1)∩{z | state z=code r.1 r.2}
  refine ⟨n,code,piece,?_,?_,?_,?_,?_,?_⟩
  · intro v
    simp [n]
  · intro r
    exact (hE.inter (hHist r.1)).inter (hstate (measurableSet_singleton _))
  · intro r z hz
    exact hz.1
  · rintro ⟨v,j⟩ ⟨w,l⟩ hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    by_cases hvw : v=w
    · subst w
      have hcode : code v j=code v l := hz.2.symm.trans hz'.2
      have hjl : j=l := (Fintype.equivFin ↥(menus v)).symm.injective (Subtype.ext hcode)
      subst l
      exact hne rfl
    · exact (Set.disjoint_left.mp (hHistDisj hvw)) hz.1.2 hz'.1.2
  · intro r z hz
    exact hz.2
  · intro z hz hzc
    obtain ⟨v,hv⟩ := hzc
    let c : ↥(menus v) := ⟨state z,hmenu v z ⟨hz,hv⟩⟩
    let j : Fin (n v) := Fintype.equivFin ↥(menus v) c
    refine ⟨⟨v,j⟩,⟨hz,hv⟩,?_⟩
    change state z=((Fintype.equivFin ↥(menus v)).symm ((Fintype.equivFin ↥(menus v)) c)).1
    rw [Equiv.symm_apply_apply]

/-- All coarser query grids use this bounded neighborhood of the
fixed reference cell's corner. Its cardinality is independent of the
position, absolute reference mesh and chosen query scale. -/
def referenceCellOptions {n : ℕ} (referenceMesh queryMesh : Fin n → ℝ)
    (q : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  integerCodeBox 1 (fun j => ⌊referenceMesh j*(q j:ℝ)/queryMesh j⌋)

theorem card_referenceCellOptions {n : ℕ} (referenceMesh queryMesh : Fin n → ℝ)
    (q : Fin n → ℤ) : (referenceCellOptions referenceMesh queryMesh q).card=3^n := by
  simp [referenceCellOptions,card_integerCodeBox]

/-- A reference-cell record has at most3^n codes in EVERY coarser
coordinate grid; the record partition never depends on that query. -/
theorem mem_referenceCellOptions {n : ℕ} (referenceMesh queryMesh : Fin n → ℝ)
    (href : ∀ j, 0 < referenceMesh j) (hquery : ∀ j, 0 < queryMesh j)
    (hsize : ∀ j, referenceMesh j ≤ queryMesh j)
    (q : Fin n → ℤ) (x : Fin n → ℝ)
    (hcode : (fun j => ⌊x j/referenceMesh j⌋)=q) :
    (fun j => ⌊x j/queryMesh j⌋)∈referenceCellOptions referenceMesh queryMesh q := by
  apply floor_code_mem_integerCodeBox 1 x (fun j => referenceMesh j*(q j:ℝ))
    queryMesh hquery
  intro j
  have hj : ⌊x j/referenceMesh j⌋=q j := congrFun hcode j
  have hlo := Int.floor_le (x j/referenceMesh j)
  have hhi := Int.lt_floor_add_one (x j/referenceMesh j)
  rw [hj] at hlo hhi
  have hleft : referenceMesh j*(q j:ℝ) ≤ x j := by
    have h := (le_div_iff₀ (href j)).mp hlo
    nlinarith only [h]
  have hright : x j < referenceMesh j*((q j:ℝ)+1) := by
    have h := (div_lt_iff₀ (href j)).mp hhi
    nlinarith only [h]
  simp only [Nat.cast_one,one_mul]
  rw [abs_le]
  constructor <;> nlinarith [href j,hsize j]

/-- Any option for one record pads every other code of that record by
at most two integer steps. This gives5^n padding cells simultaneously
for all coarser queried grids. -/
theorem referenceCellOptions_padding {n : ℕ} (referenceMesh queryMesh : Fin n → ℝ)
    (q z z' : Fin n → ℤ)
    (hz : z∈referenceCellOptions referenceMesh queryMesh q)
    (hz' : z'∈referenceCellOptions referenceMesh queryMesh q) :
    z'∈integerCodeBox 2 z := by
  rw [referenceCellOptions,mem_integerCodeBox] at hz hz'
  rw [mem_integerCodeBox]
  intro j
  have h := hz j
  have h' := hz' j
  constructor <;> omega

/-- A short actual menu at ONE fixed finest coordinate grid produces
measurable disjoint records before ALL query meshes. Each record meets
at most3^dimension coarser cells and has5^dimension padding around ANY
one of those options. This is signal agnostic and uses no pair oracle. -/
theorem exists_history_grid_records
    {Ω Index : Type*} [MeasurableSpace Ω] {dimension : ℕ}
    (E : Set Ω) (hE : MeasurableSet E)
    (Hist : Index → Set Ω) (hHist : ∀ v, MeasurableSet (Hist v))
    (hHistDisj : Pairwise (fun v w => Disjoint (Hist v) (Hist w)))
    (coords : Ω → Fin dimension → ℝ) (hcoords : Measurable coords)
    (referenceMesh : Fin dimension → ℝ) (href : ∀ j, 0 < referenceMesh j)
    (menus : Index → Finset (Fin dimension → ℤ))
    (hmenu : ∀ v, ∀ z∈E∩Hist v, (fun j => ⌊coords z j/referenceMesh j⌋)∈menus v) :
    ∃ (n : Index → ℕ) (code : (v : Index) → Fin (n v) → (Fin dimension → ℤ))
      (piece : (Σ v, Fin (n v)) → Set Ω),
      (∀ v, n v=(menus v).card) ∧
      (∀ r, MeasurableSet (piece r)) ∧
      (∀ r, piece r ⊆ E∩Hist r.1) ∧
      Pairwise (fun r s => Disjoint (piece r) (piece s)) ∧
      (∀ z∈E, (∃ v, z∈Hist v) → ∃ r, z∈piece r) ∧
      ∀ queryMesh : Fin dimension → ℝ, (∀ j, 0 < queryMesh j) →
        (∀ j, referenceMesh j ≤ queryMesh j) →
        ∀ r,
          (referenceCellOptions referenceMesh queryMesh (code r.1 r.2)).card=3^dimension ∧
          (∀ z∈piece r, (fun j => ⌊coords z j/queryMesh j⌋)∈
            referenceCellOptions referenceMesh queryMesh (code r.1 r.2)) ∧
          ∀ q∈referenceCellOptions referenceMesh queryMesh (code r.1 r.2),
            (integerCodeBox 2 q).card=5^dimension ∧
            ∀ z∈piece r, (fun j => ⌊coords z j/queryMesh j⌋)∈integerCodeBox 2 q := by
  have hstate : Measurable (fun z j => ⌊coords z j/referenceMesh j⌋) := by
    apply measurable_pi_iff.mpr
    intro j
    exact Int.measurable_floor.comp (((measurable_pi_apply j).comp hcoords).div_const _)
  obtain ⟨n,code,piece,hn,hm,hs,hd,hcode,hcover⟩ := exists_history_menu_records
    E hE Hist hHist hHistDisj (fun z j => ⌊coords z j/referenceMesh j⌋) hstate menus hmenu
  refine ⟨n,code,piece,hn,hm,hs,hd,hcover,?_⟩
  intro queryMesh hquery hsize r
  have hoptions (z : Ω) (hz : z∈piece r) :
      (fun j => ⌊coords z j/queryMesh j⌋)∈
        referenceCellOptions referenceMesh queryMesh (code r.1 r.2) :=
    mem_referenceCellOptions referenceMesh queryMesh href hquery hsize _ _ (hcode r z hz)
  refine ⟨card_referenceCellOptions _ _ _,hoptions,?_⟩
  intro q hq
  refine ⟨?_,fun z hz => referenceCellOptions_padding _ _ _ _ _ hq (hoptions z hz)⟩
  simp [card_integerCodeBox]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
