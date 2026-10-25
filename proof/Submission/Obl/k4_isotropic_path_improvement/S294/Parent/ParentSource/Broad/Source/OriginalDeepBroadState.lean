-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalDeepBroadState, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalDeepBroadState.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalDeepBroadState.lean.
All earlier source attributions below are retained.
Renamed `exists_original_deep_broad_state` to `exists_original_deep_broad_state_on_source`
(x1035 owns a different theorem of the old name in this obligation). -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.BroadParent
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PreparedAncestry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory

noncomputable section

/-- A whole actual deep packet meeting a broad original source has ONE
active old parent and ONE intrinsic broad fine state. Prepared uniqueness
handles block endpoints, and the conclusion covers every source point in
that deep packet, not just the witness used to select its old parent. -/
theorem BroadResidual.exists_original_deep_broad_state_on_source
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ}
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ) (hio : i ≤ stop)
    (source : Fin (d.W k) → Set Ev) (hsource : ∀ w, source w⊆broad.residual w)
    (deep : Fin p.C) (hdeep : p.lev deep=stop)
    (hne : (source (p.γ deep)∩p.F deep).Nonempty) :
    ∃ old : Fin p.C, p.lev old=i ∧ p.γ old=p.γ deep ∧ F.active old ∧
      F.coding.code deep∉Q.intrinsicNarrowStates F.code stop F.U r fraction old ∧
      F.coding.code deep∉fineRetentionFailures (Q.coarseLaw (p.lev old) (F.code old))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U old) (ENNReal.ofReal (1/8:ℝ)) ∧
      ∀ z∈source (p.γ deep)∩p.F deep, z∈F.fineOriginalEvent old deep univ := by
  obtain ⟨z₀,hz₀source,hz₀deep⟩ := hne
  have hz₀broad := hsource _ hz₀source
  obtain ⟨old,hold,hγold,hz₀old,hactive,_⟩ := broad.witness _ _ hz₀broad
  have hz₀base := Q.residual_subset _ (broad.subset_prepared _ hz₀broad)
  have hsub : p.F deep⊆p.F old := Q.original_ancestor_of_common_incidence hp old deep
    (by rw [hold,hdeep]; exact hio) hγold.symm z₀ (by rw [hγold]; exact hz₀base) hz₀old hz₀deep
  have hfit (z : Ev) (hz : z∈source (p.γ deep)∩p.F deep) :
      F.coding.code deep∉Q.intrinsicNarrowStates F.code stop F.U r fraction old ∧
      F.coding.code deep∉fineRetentionFailures (Q.coarseLaw (p.lev old) (F.code old))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U old) (ENNReal.ofReal (1/8:ℝ)) ∧
      z∈F.fineOriginalEvent old deep univ := by
    have hzold : z∈broad.residual (p.γ old)∩p.F old := by
      rw [hγold]
      exact ⟨hsource _ hz.1,hsub hz.2⟩
    obtain ⟨f,hf,hγf,he,hret,hevent⟩ := broad.original_parent_fine_cover old hold z hzold
    have hzFf : z∈p.F f := by
      have hh := hevent.1
      simp only [PathData.packetWitness,ite_eq_left (show p.lev f=stop ∧ p.γ f=p.γ old from ⟨hf,hγf⟩)] at hh
      exact hh.1.1
    have hzbase := Q.residual_subset _ (broad.subset_prepared _ (hsource _ hz.1))
    have hfeq : f=deep := Q.base_packet_unique (p.γ deep) z hzbase f deep
      (hf.trans hdeep.symm) (hγf.trans hγold) rfl hzFf hz.2
    subst f
    exact ⟨he,hret,hevent⟩
  have hfirst := hfit z₀ ⟨hz₀source,hz₀deep⟩
  exact ⟨old,hold,hγold,hactive,hfirst.1,hfirst.2.1,fun z hz => (hfit z hz).2.2⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
