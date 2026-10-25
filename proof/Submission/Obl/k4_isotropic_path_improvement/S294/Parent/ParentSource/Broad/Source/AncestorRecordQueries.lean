-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorRecordQueries, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ReferenceRecordCharts
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorHistoryGridRecords
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorSignalCoordinates

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set Native
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
open Submission.Lib.K4ListedExceptions

noncomputable section

/-- The one finest root partition serves every later unsheared packet
chart whose physical query cells resolve that partition. All actual
chart translations cancel before any cell menu is chosen. -/
theorem ancestor_record_query_menus
    {W : ℕ} {p : PathData W} {Rec : Type*}
    (N : ℝ) (root child : Fin p.C)
    (piece : Rec → Set Ev) (code : Rec → Fin 4 → ℤ)
    {baseRef hiddenRef baseQuery hiddenQuery : ℝ}
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef)
    (hbaseQuery : 0 < baseQuery) (hhiddenQuery : 0 < hiddenQuery)
    (hrecords : ∀ r z, z∈piece r →
      (fun j => ⌊parentUnshearedCoordinates N p root (p.R root) z j /
        ((Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef : Fin 4 → ℝ) j)⌋)∈
      referenceCellOptions
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef)
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef) (code r))
    (hbaseBudget : 3*((2:ℝ)^p.T (p.lev child)/(2:ℝ)^p.T (p.lev root))*baseRef ≤ baseQuery)
    (hhiddenBudget : 3*(δ N (p.r (p.lev root))/δ N (p.r (p.lev child)))*hiddenRef ≤ hiddenQuery) :
    ∃ options : Rec → Finset (Fin 4 → ℤ),
      (∀ r, (options r).card ≤ 81) ∧
      (∀ r z, z∈piece r →
        (fun j => ⌊parentUnshearedCoordinates N p child (p.R root) z j /
          ((Fin.snoc (fun _ : Fin 3 => baseQuery) hiddenQuery : Fin 4 → ℝ) j)⌋)∈options r) ∧
      ∀ r q, q∈options r → ∀ z∈piece r,
        (fun j => ⌊parentUnshearedCoordinates N p child (p.R root) z j /
          ((Fin.snoc (fun _ : Fin 3 => baseQuery) hiddenQuery : Fin 4 → ℝ) j)⌋)∈integerCodeBox 2 q := by
  let referenceMesh : Fin 4 → ℝ := Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef
  let mesh : Fin 4 → ℝ := Fin.snoc (fun _ : Fin 3 => baseQuery) hiddenQuery
  have href : ∀ j, 0 < referenceMesh j := by
    intro j
    refine Fin.lastCases ?_ (fun _ => ?_) j
    · simpa only [referenceMesh,Fin.snoc_last] using hhiddenRef
    · simpa only [referenceMesh,Fin.snoc_castSucc] using hbaseRef
  have hmesh : ∀ j, 0 < mesh j := by
    intro j
    refine Fin.lastCases ?_ (fun _ => ?_) j
    · simpa only [mesh,Fin.snoc_last] using hhiddenQuery
    · simpa only [mesh,Fin.snoc_castSucc] using hbaseQuery
  have hdiam r z (hz : z∈piece r) w (hw : w∈piece r) : ∀ j,
      |parentUnshearedCoordinates N p child (p.R root) z j-
        parentUnshearedCoordinates N p child (p.R root) w j| ≤ mesh j := by
    have hroot := reference_options_coordinate_diameter referenceMesh href (code r)
      (parentUnshearedCoordinates N p root (p.R root) z)
      (parentUnshearedCoordinates N p root (p.R root) w) (hrecords r z hz) (hrecords r w hw)
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [parentUnshearedCoordinates,Fin.snoc_last,mesh] at hroot ⊢
      have hfactor : 0 ≤ δ N (p.r (p.lev root))/δ N (p.r (p.lev child)) := by
        unfold δ
        positivity
      have hsignal : |packetSignal N p root z-packetSignal N p root w| ≤ 3*hiddenRef := by
        simpa only [parentUnshearedCoordinates,Fin.snoc_last,referenceMesh,
          physicalParentSignal,packetSignal] using hroot (Fin.last 3)
      rw [ancestor_signal_in_child_units N p root child z,
        ancestor_signal_in_child_units N p root child w,←mul_sub,abs_mul,abs_of_nonneg hfactor]
      exact (mul_le_mul_of_nonneg_left hsignal hfactor).trans
        (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hhiddenBudget)
    · simp only [parentUnshearedCoordinates,Fin.snoc_castSucc,mesh]
      have hfactor : 0 ≤ (2:ℝ)^p.T (p.lev child)/(2:ℝ)^p.T (p.lev root) := by positivity
      have hcoord : |unshearedPacketBase p root z i-unshearedPacketBase p root w i| ≤ 3*baseRef := by
        simpa only [parentUnshearedCoordinates,Fin.snoc_castSucc,referenceMesh] using hroot i.castSucc
      rw [unsheared_base_difference_between_clocks p child root z w i,abs_mul,abs_of_nonneg hfactor]
      exact (mul_le_mul_of_nonneg_left hcoord hfactor).trans
        (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hbaseBudget)
  simpa only [show (3:ℕ)^4=81 by norm_num] using
    exists_record_grid_menus piece (parentUnshearedCoordinates N p child (p.R root)) mesh hmesh hdiam

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
