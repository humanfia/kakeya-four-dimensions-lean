-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalDeepAncestorSignalMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalDeepAncestorSignalMenus.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
/- Adapted from this tree's OriginalDeepMenus.lean. The original
 o265/session x0943 attribution and earlier credits are preserved below. -/
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalDeepMenus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RetainedAncestorSignalMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PreparedAncestry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.LocalReferences

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ ε : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- Every true whole deep history has a short menu for the fixed ancestor
signal in the selected child's units. Intermediate fine ancestry and its
full counted-set inclusion are derived from the original parent chain and
prepared uniqueness. No ancestry, pair-bound or later mass oracle is used. -/
theorem ValueBranchData.exists_original_deep_ancestor_signal_menus
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    (root child : Fin p.C) (stop : ℕ) (hmid : p.lev root ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r (p.lev root)))
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hbaseSmall : ∀ deep : Fin p.C, p.lev deep = stop →
      p.unshearedDeepRadius child deep ≤ baseMesh)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine = mid → p.lev deep = stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K ^ R)⁻¹ / 12)
    (hheightSmall : ∀ fine deep : Fin p.C, p.lev fine = mid → p.lev deep = stop →
      (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*
        (2 * (K ^ 14 * (K ^ 6)⁻¹ *
          (δ (d.N k) (p.r mid) / δ (d.N k) (p.r (p.lev root)))) +
          ((K ^ (qcore + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
            (6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ fine deep)) ≤ hidden) :
    ∃ menus : ↥(originalFinePackets p root stop) → Finset (Fin 4 → ℤ),
      (∀ deep, ((menus deep).card : ℝ) ≤ K ^ 12) ∧
      ∀ deep, ∀ z ∈ V.coreRetained cores (p.γ root) ∩ p.F deep.1,
        jointCode baseMesh hidden (fun j => unshearedPacketBase p child z j)
          (physicalParentSignal (d.N k) p child (p.R root) z) ∈ menus deep := by
  classical
  have hKpos : 0 < K := by linarith
  have hBworld : ∀ w, 0 < d.B k w := by
    obtain ⟨_, _, _, _, _, _, _, _, hformat, _⟩ := hd
    obtain ⟨M, D, hformat⟩ := hformat
    intro w
    exact ((hformat k).2.2.2.1 w).2.1
  have hex (deep : ↥(originalFinePackets p root stop)) :
      ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card : ℝ) ≤ K ^ 12 ∧
        ∀ z ∈ V.coreRetained cores (p.γ root) ∩ p.F deep.1,
          jointCode baseMesh hidden (fun j => unshearedPacketBase p child z j)
          (physicalParentSignal (d.N k) p child (p.R root) z) ∈ Menu := by
    have hdeep := (Finset.mem_filter.mp deep.2).2
    let U := V.coreRetained cores (p.γ root) ∩ p.F deep.1
    by_cases hU : U.Nonempty
    · obtain ⟨z, hz⟩ := hU
      have hzbase : z ∈ Q.base (p.γ root) := hHbase _ (V.residual_subset _ hz.1.1)
      have hzold : z ∈ p.F root := hdeep.2.2 hz.2
      have hdiff : stop - mid ≤ p.lev deep.1 := by omega
      let fine := p.par^[stop - mid] deep.1
      obtain ⟨hl, hg, hF⟩ := Broad.iterate_par_spec hp.toOriginal (stop - mid) deep.1 hdiff
      change p.lev fine = p.lev deep.1 - (stop - mid) at hl
      change p.γ fine = p.γ deep.1 at hg
      change p.F deep.1 ⊆ p.F fine at hF
      have hfine : p.lev fine = mid := by omega
      have hγfine : p.γ fine = p.γ root := hg.trans hdeep.2.1
      have hAfine : p.A deep.1 ⊆ p.A fine := hp.iterate_par_assignment (stop - mid) deep.1 hdiff
      have hFold : p.F fine ⊆ p.F root := Q.original_ancestor_of_common_incidence hp
        root fine (by omega) hγfine z hzbase hzold (hF hz.2)
      exact V.exists_deep_ancestor_signal_source_menu Q hpure hd hp hHE hHbase hK hmax hpower hκK
        fine hfine hr hrL (hBworld _) cores hD hjets root child deep.1 hγfine
        (by simpa only [hfine] using hwidth) hFold hAfine hF hbase hhidden
        (hbaseSmall deep.1 hdeep.1)
        (by simpa only [hfine] using hheightSmall fine deep.1 hfine hdeep.1)
        (hcoreSmall fine deep.1 hfine hdeep.1)
    · refine ⟨∅, by simp; positivity, ?_⟩
      intro z hz
      exact (hU ⟨z, hz⟩).elim
  choose menus hcard hcover using hex
  exact ⟨menus, hcard, hcover⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
