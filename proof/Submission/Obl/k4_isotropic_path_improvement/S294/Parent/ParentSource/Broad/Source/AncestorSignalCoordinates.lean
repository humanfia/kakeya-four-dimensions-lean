-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorSignalCoordinates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AncestorSignalCoordinates.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RootRowStateMenus
import Submission.Lib.K4JointResolutionSupport

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native

noncomputable section

/-- The exact scalar relation of the original unsheared bases also holds
for their Euclidean differences. All actual chart translations cancel. -/
theorem norm_unsheared_base_difference_between_clocks {W : ℕ}
    (p : PathData W) (root child : Fin p.C) (z w : Ev) :
    ‖unshearedPacketBase p root z-unshearedPacketBase p root w‖=
      ((2 : ℝ)^p.T (p.lev root)/(2 : ℝ)^p.T (p.lev child))*
        ‖unshearedPacketBase p child z-unshearedPacketBase p child w‖ := by
  have heq : unshearedPacketBase p root z-unshearedPacketBase p root w=
      ((2 : ℝ)^p.T (p.lev root)/(2 : ℝ)^p.T (p.lev child)) •
        (unshearedPacketBase p child z-unshearedPacketBase p child w) := by
    ext j
    exact unsheared_base_difference_between_clocks p root child z w j
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]

/-- Reading a fixed actual ancestor test in a child's thickness units
changes its signal by the exact relative thickness factor. -/
theorem ancestor_signal_in_child_units {W : ℕ} (N : ℝ) (p : PathData W)
    (root child : Fin p.C) (z : Ev) :
    physicalParentSignal N p child (p.R root) z=
      (δ N (p.r (p.lev root))/δ N (p.r (p.lev child)))*packetSignal N p root z := by
  have ha : δ N (p.r (p.lev root))≠0 := by unfold δ; positivity
  unfold physicalParentSignal packetSignal
  field_simp

/-- A genuine whole-core pair bound for R_root/a_root passes to the
literal later coordinates. The slope has ONLY the relative clock and
thickness ratios, with no absolute h_root/a_root factor. -/
theorem ancestor_signal_pair_in_child_units {W : ℕ} (N : ℝ) (p : PathData W)
    (root child : Fin p.C) (z w : Ev) {additive Lip : ℝ}
    (hpair : |packetSignal N p root z-packetSignal N p root w| ≤
      additive+Lip*‖unshearedPacketBase p root z-unshearedPacketBase p root w‖) :
    |physicalParentSignal N p child (p.R root) z-
        physicalParentSignal N p child (p.R root) w| ≤
      (δ N (p.r (p.lev root))/δ N (p.r (p.lev child)))*additive+
      ((δ N (p.r (p.lev root))/δ N (p.r (p.lev child)))*Lip*
        ((2 : ℝ)^p.T (p.lev root)/(2 : ℝ)^p.T (p.lev child)))*
          ‖unshearedPacketBase p child z-unshearedPacketBase p child w‖ := by
  have hfactor : 0 < δ N (p.r (p.lev root))/δ N (p.r (p.lev child)) := by
    unfold δ
    positivity
  rw [ancestor_signal_in_child_units N p root child z,
    ancestor_signal_in_child_units N p root child w,←mul_sub,abs_mul,abs_of_pos hfactor]
  apply (mul_le_mul_of_nonneg_left hpair hfactor.le).trans
  rw [norm_unsheared_base_difference_between_clocks p root child z w]
  exact le_of_eq (by ring)

/-- The later joint mesh condition uses the RELATIVE aspect ratio.
This pays the signal slope with no inverse absolute ancestor width. -/
theorem ancestor_signal_joint_slope_budget {W : ℕ} (N : ℝ) (p : PathData W)
    (root child : Fin p.C) {Lip base hidden : ℝ}
    (hbase : 0 ≤ base) (hhidden : 0 < hidden)
    (hmesh : 6*Lip*((2 : ℝ)^p.T (p.lev root)/(2 : ℝ)^p.T (p.lev child))*base ≤
      (δ N (p.r (p.lev child))/δ N (p.r (p.lev root)))*hidden) :
    6*((((δ N (p.r (p.lev root))/δ N (p.r (p.lev child)))*Lip*
      ((2 : ℝ)^p.T (p.lev root)/(2 : ℝ)^p.T (p.lev child)))*base)/hidden) ≤ 1 := by
  have haRoot : δ N (p.r (p.lev root))≠0 := by unfold δ; positivity
  have haChild : δ N (p.r (p.lev child))≠0 := by unfold δ; positivity
  have ha : 0 < δ N (p.r (p.lev child))/δ N (p.r (p.lev root)) := by
    unfold δ
    positivity
  apply Submission.Lib.K4JointResolutionSupport.physical_parent_joint_slope_budget
    ha hbase hhidden (le_of_eq ?_) hmesh
  field_simp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
