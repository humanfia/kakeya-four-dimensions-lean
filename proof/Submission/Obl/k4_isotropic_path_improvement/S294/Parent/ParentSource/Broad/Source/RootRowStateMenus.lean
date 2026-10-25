-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.RootRowStateMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/RootRowStateMenus.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockGridCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentMovingBandCap
import Submission.Lib.K4ListedExceptions.FrameCodes
import Submission.Obl.k4_oss_collision_cauchy_schwarz.Cells

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4ListedExceptions

noncomputable section

/-- Translations of the two original old frames cancel in differences.
Only their actual scalar clock ratio remains. No equality of the chart
centers or velocities, and no new coordinate frame, is assumed. -/
theorem unsheared_base_difference_between_clocks {W : ℕ} (p : PathData W)
    (root child : Fin p.C) (z w : Ev) (j : Fin 3) :
    unshearedPacketBase p root z j-unshearedPacketBase p root w j=
      ((2 : ℝ)^p.T (p.lev root)/(2 : ℝ)^p.T (p.lev child))*
        (unshearedPacketBase p child z j-unshearedPacketBase p child w j) := by
  fin_cases j <;> simp [unshearedPacketBase] <;> field_simp <;> ring

/-- The scalar signal read in the root clock is exactly the child's
physical P/a signal multiplied by aChild/hRoot. -/
theorem clock_signal_difference_from_physical {W : ℕ} (N : ℝ) (p : PathData W)
    (root child : Fin p.C) (P : Po) (z w : Ev) :
    clockParentSignal p root P z-clockParentSignal p root P w=
      ((2 : ℝ)^p.T (p.lev root)*δ N (p.r (p.lev child)))*
        (physicalParentSignal N p child P z-physicalParentSignal N p child P w) := by
  have ha : δ N (p.r (p.lev child))≠0 := by unfold δ; positivity
  unfold clockParentSignal physicalParentSignal
  field_simp

/-- Every literal later physical state has at most 81 compatible ROOT
row codes, independently of all frame offsets. These are the original
root P/h codes; the later code is the actual physical P/a product code. -/
theorem root_row_menus_over_later_physical_states {W : ℕ}
    (N : ℝ) (p : PathData W) (root child : Fin p.C) (P : Po)
    {fine rowMesh : ℝ} (hfine : 0 < fine) (hrow : 0 < rowMesh)
    (hbase : ((2 : ℝ)^p.T (p.lev root)/(2 : ℝ)^p.T (p.lev child))*fine ≤ rowMesh)
    (hheight : ((2 : ℝ)^p.T (p.lev root)*δ N (p.r (p.lev child)))*fine ≤ rowMesh) :
    ∃ menu : ((Fin 3 → ℤ) × ℤ) → Finset (Fin 4 → ℤ),
      (∀ q, (menu q).card ≤ 81) ∧
      ∀ z : Ev, clockParentCode p root P rowMesh z∈menu
        (gridCode (fun z j => unshearedPacketBase p child z j)
          (physicalParentSignal N p child P) fine fine z) := by
  classical
  let fineCode := gridCode (fun z j => unshearedPacketBase p child z j)
    (physicalParentSignal N p child P) fine fine
  have hclose {z w : Ev} (heq : fineCode z=fineCode w) (j : Fin 4) :
      |clockParentCoordinates p root P z j-clockParentCoordinates p root P w j| ≤ rowMesh := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [clockParentCoordinates,Fin.snoc_last]
      have hh := Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell
        hfine (congrArg Prod.snd heq)
      rw [clock_signal_difference_from_physical N p root child P z w,abs_mul]
      have hfactor : 0 ≤ (2 : ℝ)^p.T (p.lev root)*δ N (p.r (p.lev child)) := by
        unfold δ
        positivity
      rw [abs_of_nonneg hfactor]
      exact (mul_le_mul_of_nonneg_left hh hfactor).trans hheight
    · simp only [clockParentCoordinates,Fin.snoc_castSucc]
      have hh := Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell
        hfine (congrArg (fun q : (Fin 3 → ℤ) × ℤ => q.1 i) heq)
      rw [unsheared_base_difference_between_clocks p root child z w i,abs_mul]
      have hfactor : 0 ≤ (2 : ℝ)^p.T (p.lev root)/(2 : ℝ)^p.T (p.lev child) := by positivity
      rw [abs_of_nonneg hfactor]
      exact (mul_le_mul_of_nonneg_left hh hfactor).trans hbase
  have hlocal {z w : Ev} (heq : fineCode z=fineCode w) :
      clockParentCode p root P rowMesh z∈integerCodeBox 1 (clockParentCode p root P rowMesh w) := by
    apply floor_code_mem_integerCodeBox 1 (clockParentCoordinates p root P z)
      (clockParentCoordinates p root P w) (fun _ => rowMesh) (fun _ => hrow)
    intro j
    simpa only [Nat.cast_one,one_mul] using hclose heq j
  have hmenu (q : (Fin 3 → ℤ) × ℤ) :
      ∃ F : Finset (Fin 4 → ℤ), F.card ≤ 81 ∧
        ∀ z : Ev, fineCode z=q → clockParentCode p root P rowMesh z∈F := by
    by_cases hq : ∃ w : Ev, fineCode w=q
    · obtain ⟨w,hw⟩ := hq
      refine ⟨integerCodeBox 1 (clockParentCode p root P rowMesh w),?_,?_⟩
      · rw [card_integerCodeBox]
        norm_num
      · intro z hz
        exact hlocal (hz.trans hw.symm)
    · exact ⟨∅,by simp,fun z hz => (hq ⟨z,hz⟩).elim⟩
  choose menu hcard hcover using hmenu
  exact ⟨menu,hcard,fun z => hcover (fineCode z) z rfl⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
