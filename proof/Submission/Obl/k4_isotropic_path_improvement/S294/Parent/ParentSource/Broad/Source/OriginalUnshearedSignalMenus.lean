-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalUnshearedSignalMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalUnshearedSignalMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalUnshearedSignalMenus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RetainedUnshearedSignalMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PreparedAncestry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- Choose the real intermediate ancestor of each whole deep packet
internally. The resulting physical signal menus use all retained value
bins and cores and have no selected-entry mass hypothesis. -/
theorem ValueBranchData.exists_original_unsheared_signal_deep_menus
    (hHbase : ∀ w, H w⊆Q.base w) (hK : 2304 ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K^qcore)⁻¹)))
    (old : Fin p.C) (stop : ℕ) (hstop : mid ≤ stop)
    (source : Set Event) (hsource : source⊆V.coreRetained cores (p.γ old))
    (signal : Event → ℝ) {additive Lip base hidden : ℝ} (hLip : 0 ≤ Lip)
    (hbase : 0 < base) (hhidden : 0 < hidden)
    (hbaseSmall : ∀ deep : Fin p.C, p.lev deep=stop → p.unshearedDeepRadius old deep ≤ base)
    (hheightSmall : ∀ deep : Fin p.C, p.lev deep=stop →
      additive+Lip*(6*p.unshearedDeepRadius old deep) ≤ hidden)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K^R)⁻¹/12)
    (hpair : ∀ (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool),
      p.γ v.1.1=p.γ old →
      ∀ z∈source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci),
      ∀ z'∈source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci),
        |signal z-signal z'| ≤ additive+Lip*
          ‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖) :
    ∃ menus : ↥(originalFinePackets p old stop) → Finset (Fin 4 → ℤ),
      (∀ deep, ((menus deep).card:ℝ) ≤ K^12) ∧
      ∀ deep, ∀ z∈source∩p.F deep.1,
        jointCode base hidden (fun j => unshearedPacketBase p old z j) (signal z)∈menus deep := by
  classical
  have hex (deep : ↥(originalFinePackets p old stop)) :
      ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card:ℝ) ≤ K^12 ∧
      ∀ z∈source∩p.F deep.1,
        jointCode base hidden (fun j => unshearedPacketBase p old z j) (signal z)∈Menu := by
    have hdeep := (Finset.mem_filter.mp deep.2).2
    by_cases hU : (source∩p.F deep.1).Nonempty
    · obtain ⟨z,hz⟩ := hU
      have hdiff : stop-mid ≤ p.lev deep.1 := by omega
      let fine := p.par^[stop-mid] deep.1
      obtain ⟨hl,hg,hF⟩ := Broad.iterate_par_spec hp.toOriginal (stop-mid) deep.1 hdiff
      change p.lev fine=p.lev deep.1-(stop-mid) at hl
      change p.γ fine=p.γ deep.1 at hg
      change p.F deep.1⊆p.F fine at hF
      have hfine : p.lev fine=mid := by omega
      have hγfine : p.γ fine=p.γ old := hg.trans hdeep.2.1
      have hAfine : p.A deep.1⊆p.A fine := hp.iterate_par_assignment (stop-mid) deep.1 hdiff
      exact V.exists_deep_retained_unsheared_signal_menu Q hd hp hHbase hK cores fine hfine
        old deep.1 hγfine hAfine hF source hsource signal hLip hbase hhidden
        (hbaseSmall deep.1 hdeep.1) (hheightSmall deep.1 hdeep.1)
        (hcoreSmall fine deep.1 hfine hdeep.1) hpair
    · refine ⟨∅,by simp; positivity,?_⟩
      intro z hz
      exact (hU ⟨z,hz⟩).elim
  choose menus hcard hcover using hex
  exact ⟨menus,hcard,hcover⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
