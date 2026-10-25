-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.RetainedAncestorHistories, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.BroadParent
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PreparedAncestry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineOriginalPosterior

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ)

/-- The actual full descendant list filtered by the original retention
criterion. This is a finite family of unchanged original histories. -/
def Native.PaletteFamily.retainedOriginalFinePackets (root : Fin p.C) : Finset (Fin p.C) := by
  classical
  exact (originalFinePackets p root stop).filter fun fine =>
    F.coding.code fine∉fineRetentionFailures (Q.coarseLaw (p.lev root) (F.code root))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U root) (ENNReal.ofReal (1/8:ℝ))

theorem Native.PaletteFamily.retained_original_fine_spec
    (root : Fin p.C) (fine : ↥(F.retainedOriginalFinePackets root)) :
    fine.1∈originalFinePackets p root stop ∧
      F.coding.code fine.1∉fineRetentionFailures (Q.coarseLaw (p.lev root) (F.code root))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U root) (ENNReal.ofReal (1/8:ℝ)) := by
  classical
  exact Finset.mem_filter.mp fine.2

variable {r fraction κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (broad : BroadResidual F r fraction)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hp

/-- Every original broad incidence belongs to an actual retention-good
full descendant history. Its inclusion in the ancestor is DERIVED from
the real parent chain and the prepared uniqueness mask. -/
theorem Native.BroadResidual.exists_retained_original_fine_history
    (hio : i ≤ stop) (root : Fin p.C) (hroot : p.lev root=i)
    (z : Ev) (hz : z∈broad.residual (p.γ root)∩p.F root) :
    ∃ fine : ↥(F.retainedOriginalFinePackets root),
      z∈F.fineOriginalEvent root fine.1 univ := by
  classical
  obtain ⟨fine,hfine,hworld,_hwide,hretained,hevent⟩ :=
    broad.original_parent_fine_cover root hroot z hz
  have hbase : z∈Q.base (p.γ root) := Q.residual_subset _ (broad.subset_prepared _ hz.1)
  have hzFine : z∈p.F fine := by
    have hh : (z∈p.F fine ∧ packetUnique p.lev p.γ p.F (p.γ root) z) ∧
        z∈p.terminalCoverage m (p.γ root) := by
      simpa only [PathData.packetWitness,ite_eq_left (And.intro hfine hworld),
        mem_inter_iff,mem_ofPred_eq] using hevent.1
    exact hh.1.1
  have hsub : p.F fine⊆p.F root := Q.original_ancestor_of_common_incidence hp
    root fine (by rw [hroot,hfine]; exact hio) hworld z hbase hz.2 hzFine
  have hmem : fine∈originalFinePackets p root stop :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfine,hworld,hsub⟩
  exact ⟨⟨fine,Finset.mem_filter.mpr ⟨hmem,hretained⟩⟩,hevent⟩

/-- Every true fine history meeting the broad source satisfies its
original retention criterion. No history-specific deletion is made. -/
theorem Native.BroadResidual.retention_good_of_fine_original_event
    (hio : i ≤ stop) (root : Fin p.C) (hroot : p.lev root=i)
    (fine : ↥(originalFinePackets p root stop))
    (z : Ev) (hz : z∈broad.residual (p.γ root)∩p.F root)
    (hevent : z∈F.fineOriginalEvent root fine.1 univ) :
    F.coding.code fine.1∉fineRetentionFailures (Q.coarseLaw (p.lev root) (F.code root))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U root) (ENNReal.ofReal (1/8:ℝ)) := by
  classical
  obtain ⟨good,hgood⟩ := Native.BroadResidual.exists_retained_original_fine_history F broad hp hio root hroot z hz
  have hfine := (Finset.mem_filter.mp fine.2).2
  have hgoodSpec := F.retained_original_fine_spec root good
  have hgoodFine := (Finset.mem_filter.mp hgoodSpec.1).2
  have hpacket (f : Fin p.C) (hf : p.lev f=stop) (hw : p.γ f=p.γ root)
      (hzf : z∈F.fineOriginalEvent root f univ) : z∈p.F f := by
    have hh : (z∈p.F f ∧ packetUnique p.lev p.γ p.F (p.γ root) z) ∧
        z∈p.terminalCoverage m (p.γ root) := by
      simpa only [PathData.packetWitness,ite_eq_left (And.intro hf hw),
        mem_inter_iff,mem_ofPred_eq] using hzf.1
    exact hh.1.1
  have hbase : z∈Q.base (p.γ root) := Q.residual_subset _ (broad.subset_prepared _ hz.1)
  have heq : fine.1=good.1 := Q.base_packet_unique (p.γ root) z hbase fine.1 good.1
    (hfine.1.trans hgoodFine.1.symm) hfine.2.1 hgoodFine.2.1
    (hpacket _ hfine.1 hfine.2.1 hevent) (hpacket _ hgoodFine.1 hgoodFine.2.1 hgood)
  simpa only [heq] using hgoodSpec.2

/-- On the prepared source a true fine history meeting any earlier
packet lies entirely inside that packet. This supplies whole-record
localization when the packet is chosen after the palette pruning. -/
theorem Native.PaletteFamily.fine_original_event_whole_earlier_packet
    (root fine child : Fin p.C) (hfine : p.lev fine=stop)
    (hfworld : p.γ fine=p.γ root) (hcworld : p.γ child=p.γ root)
    (hchild : p.lev child ≤ stop)
    (z : Ev) (hz : z∈F.fineOriginalEvent root fine univ)
    (hbase : z∈Q.base (p.γ root)) (hzchild : z∈p.F child) :
    F.fineOriginalEvent root fine univ⊆p.F child := by
  have hpacket {w : Ev} (hw : w∈F.fineOriginalEvent root fine univ) : w∈p.F fine := by
    have hh : (w∈p.F fine ∧ packetUnique p.lev p.γ p.F (p.γ root) w) ∧
        w∈p.terminalCoverage m (p.γ root) := by
      simpa only [PathData.packetWitness,ite_eq_left (And.intro hfine hfworld),
        mem_inter_iff,mem_ofPred_eq] using hw.1
    exact hh.1.1
  have hsub : p.F fine⊆p.F child := Q.original_ancestor_of_common_incidence hp
    child fine (by simpa only [hfine] using hchild) (hfworld.trans hcworld.symm) z
    (by simpa only [hcworld] using hbase) hzchild (hpacket hz)
  exact fun _ hw => hsub (hpacket hw)

/-- Every true fine history meeting the broad source is intrinsically
wide. The fact applies to its full original history law. -/
theorem Native.BroadResidual.not_narrow_of_fine_original_event
    (root : Fin p.C) (hroot : p.lev root=i)
    (fine : ↥(originalFinePackets p root stop))
    (z : Ev) (hz : z∈broad.residual (p.γ root)∩p.F root)
    (hevent : z∈F.fineOriginalEvent root fine.1 univ) :
    F.coding.code fine.1∉Q.intrinsicNarrowStates F.code stop F.U r fraction root := by
  classical
  obtain ⟨good,hgood,hworld,hwide,_hretained,hgoodEvent⟩ :=
    broad.original_parent_fine_cover root hroot z hz
  have hfine := (Finset.mem_filter.mp fine.2).2
  have hpacket (f : Fin p.C) (hf : p.lev f=stop) (hw : p.γ f=p.γ root)
      (hzf : z∈F.fineOriginalEvent root f univ) : z∈p.F f := by
    have hh : (z∈p.F f ∧ packetUnique p.lev p.γ p.F (p.γ root) z) ∧
        z∈p.terminalCoverage m (p.γ root) := by
      simpa only [PathData.packetWitness,ite_eq_left (And.intro hf hw),
        mem_inter_iff,mem_ofPred_eq] using hzf.1
    exact hh.1.1
  have hbase : z∈Q.base (p.γ root) := Q.residual_subset _ (broad.subset_prepared _ hz.1)
  have heq : fine.1=good := Q.base_packet_unique (p.γ root) z hbase fine.1 good
    (hfine.1.trans hgood.symm) hfine.2.1 hworld
    (hpacket _ hfine.1 hfine.2.1 hevent) (hpacket _ hgood hworld hgoodEvent)
  simpa only [heq] using hwide

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
