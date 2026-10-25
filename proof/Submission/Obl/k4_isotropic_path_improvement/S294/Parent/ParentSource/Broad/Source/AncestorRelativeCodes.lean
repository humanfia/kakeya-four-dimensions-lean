-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorRelativeCodes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorRecordBreadthRenewal
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Forward

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set Native
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

noncomputable section

/-- The graph readout of a root query is the actual ancestor clock code. -/
theorem ancestor_root_joint_eq_clock_code
    {W : ℕ} (N : ℝ) (p : PathData W) (root : Fin p.C) (mesh : ℝ) (z : Ev) :
    jointCode mesh mesh (fun j => unshearedPacketBase p root z j)
      (physicalParentSignal N p root (p.R root) z)=
        clockParentCode p root (SignalGraph.ancestorSignal N p root) mesh z := by
  rw [ancestor_clock_code_eq_reference_floors,ancestor_joint_code_eq_coordinate_floors]
  ext j
  refine Fin.lastCases ?_ (fun _ => ?_) j <;> simp only [Fin.snoc_last,Fin.snoc_castSucc]

/-- Scale only the hidden query mesh to use the effective physical
thickness of the relative row packet. All original points remain literal. -/
theorem ancestor_child_joint_eq_physical_code
    {W : ℕ} (N : ℝ) (p : PathData W) (root child : Fin p.C)
    {aEff eps : ℝ} (haEff : 0 < aEff) (heps : 0 < eps) (z : Ev) :
    jointCode eps ((aEff/δ N (p.r (p.lev child)))*eps)
      (fun j => unshearedPacketBase p child z j)
      (physicalParentSignal N p child (p.R root) z)=
    Fin.snoc
      (O204.Tangent.physicalCode (unshearedPacketBase p child)
        (fun x => MvPolynomial.eval (xp x.1 x.2) (p.R root)/aEff) eps z).1
      (O204.Tangent.physicalCode (unshearedPacketBase p child)
        (fun x => MvPolynomial.eval (xp x.1 x.2) (p.R root)/aEff) eps z).2 := by
  have hδ : δ N (p.r (p.lev child))≠0 := by unfold δ; positivity
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [jointCode,Fin.snoc_last,O204.Tangent.physicalCode,physicalParentSignal]
    congr 1
    field_simp [hδ,haEff.ne',heps.ne'] <;> ring
  · simp only [jointCode,Fin.snoc_castSucc,O204.Tangent.physicalCode,baseCode]

/-- The four-coordinate encoding is faithful to the frozen product code. -/
theorem physical_code_eq_of_ancestor_joint_eq
    {W : ℕ} (N : ℝ) (p : PathData W) (root child : Fin p.C)
    {aEff eps : ℝ} (haEff : 0 < aEff) (heps : 0 < eps) (z z' : Ev)
    (hcode : jointCode eps ((aEff/δ N (p.r (p.lev child)))*eps)
      (fun j => unshearedPacketBase p child z j)
      (physicalParentSignal N p child (p.R root) z)=
      jointCode eps ((aEff/δ N (p.r (p.lev child)))*eps)
      (fun j => unshearedPacketBase p child z' j)
      (physicalParentSignal N p child (p.R root) z')) :
    O204.Tangent.physicalCode (unshearedPacketBase p child)
      (fun x => MvPolynomial.eval (xp x.1 x.2) (p.R root)/aEff) eps z=
    O204.Tangent.physicalCode (unshearedPacketBase p child)
      (fun x => MvPolynomial.eval (xp x.1 x.2) (p.R root)/aEff) eps z' := by
  rw [ancestor_child_joint_eq_physical_code N p root child haEff heps,
    ancestor_child_joint_eq_physical_code N p root child haEff heps] at hcode
  apply Prod.ext
  · ext j
    simpa only [Fin.snoc_castSucc] using congrFun hcode j.castSucc
  · simpa only [Fin.snoc_last] using congrFun hcode (Fin.last 3)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
