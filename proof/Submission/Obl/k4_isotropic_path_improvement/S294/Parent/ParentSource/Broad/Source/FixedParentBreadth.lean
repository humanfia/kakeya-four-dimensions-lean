-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.FixedParentBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/FixedParentBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/FixedParentBreadth.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalDeepMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalStateBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.BroadParent

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open k4_stable_native_signal_oscillation
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

/-- The actual original core source and the actual broad path produce
renewed strip breadth on the SAME physical code after arbitrary earlier
selection. The loss is charged to the full OLD prior and clock. -/
theorem ValueBranchData.exists_actual_broad_anisotropic_source
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hHterminal : ∀ w, H₀ w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (old : Fin p.C) (hold : p.lev old = i) (hactive : F.active old)
    (hmid : p.lev old ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r (p.lev old)))
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hbaseSmall : ∀ deep : Fin p.C, p.lev deep = stop →
      p.deepBaseRadius (d.N k) d.L δ₀ old deep ≤ baseMesh)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine = mid → p.lev deep = stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K ^ R)⁻¹ / 12)
    (hheightSmall : ∀ fine deep : Fin p.C, p.lev fine = mid → p.lev deep = stop →
      2 * (K ^ 14 * (K ^ 6)⁻¹ *
        (δ (d.N k) (p.r mid) / δ (d.N k) (p.r (p.lev old)))) +
        ((K ^ (qcore + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
          (6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ fine deep) ≤ hidden)
    {width : ℝ} (hfraction : 0 ≤ fraction) (hwidth0 : 0 ≤ width)
    (hstrip : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ r)
    (μ : Measure Event) (hμ : μ ≤ (d.ν k (p.γ old)).prod volume)
    (hsupport : ∀ᵐ z ∂μ, z ∈ V.coreRetained cores (p.γ old) ∩
      (broad.residual (p.γ old) ∩ p.F old))
    (δref : ENNReal) (hδ0 : δref ≠ 0) (hδtop : δref ≠ ∞) :
    ∃ keep : Set Event, MeasurableSet keep ∧
      μ univ ≤ (μ.restrict keep) univ +
        δref * ((⌈K ^ 12⌉₊ : ENNReal) * ENNReal.ofReal (p.κ ^ 2) *
          (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹))) ∧
      ∀ label (n center : EuclideanSpace ℝ (Fin 2)), ‖n‖ = 1 →
        (μ.restrict keep) {z | p.originalPhysicalCode (d.N k) old baseMesh hidden z = label ∧
          |Inner.inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity old z - center)| ≤ width} ≤
          (δref⁻¹ * ENNReal.ofReal (8 * fraction)) *
            (μ.restrict keep) {z | p.originalPhysicalCode (d.N k) old baseMesh hidden z = label} := by
  classical
  let nodes := originalFinePackets p old stop
  let good := nodes.filter (fun deep =>
    F.coding.code deep ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction old ∧
    F.coding.code deep ∉ fineRetentionFailures (Q.coarseLaw (p.lev old) (F.code old))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U old) (ENNReal.ofReal (1 / 8 : ℝ)))
  let I := ↥good
  have hn (j : I) : p.lev j.1 = stop ∧ p.γ j.1 = p.γ old ∧ p.F j.1 ⊆ p.F old :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp j.2).1).2
  have he (j : I) := (Finset.mem_filter.mp j.2).2.1
  have hret (j : I) := (Finset.mem_filter.mp j.2).2.2
  obtain ⟨rawMenus, hrawCard, hrawCover⟩ := V.exists_original_deep_menus Q hpure hd hp
    hHE hHbase hK hmax hpower hκK cores old stop hmid hstop hr hrL hD hjets hwidth
    hbase hhidden hbaseSmall hcoreSmall hheightSmall
  let menus (j : I) := rawMenus ⟨j.1, (Finset.mem_filter.mp j.2).1⟩
  have hcard (j : I) : (menus j).card ≤ ⌈K ^ 12⌉₊ := by
    exact_mod_cast (hrawCard ⟨j.1, (Finset.mem_filter.mp j.2).1⟩).trans (Nat.le_ceil _)
  have hpacket (deep : Fin p.C) (hdlev : p.lev deep = stop) (hdγ : p.γ deep = p.γ old)
      {z : Event} (hz : z ∈ F.fineOriginalEvent old deep univ) : z ∈ p.F deep := by
    have hh := hz.1
    have htag : p.lev deep = stop ∧ p.γ deep = p.γ old := ⟨hdlev, hdγ⟩
    simp only [PathData.packetWitness, ite_eq_left htag] at hh
    exact hh.1.1
  have hcover : ∀ᵐ z ∂μ, ∃ j : I, z ∈ F.fineOriginalEvent old j.1 univ := by
    filter_upwards [hsupport] with z hz
    obtain ⟨deep, hdlev, hdγ, hdnon, hdret, hzevent⟩ :=
      broad.original_parent_fine_cover old hold z hz.2
    have hzbase := hHbase _ (V.residual_subset _ hz.1.1)
    have hnode := Q.mem_original_fine_packets hp old deep stop (hmid.trans hstop) hdlev hdγ
      z hzbase hz.2.2 (hpacket deep hdlev hdγ hzevent)
    exact ⟨⟨deep, Finset.mem_filter.mpr ⟨hnode, hdnon, hdret⟩⟩, hzevent⟩
  have hmenu : ∀ᵐ z ∂μ, ∀ j : I, z ∈ F.fineOriginalEvent old j.1 univ →
      p.originalPhysicalCode (d.N k) old baseMesh hidden z ∈ menus j := by
    filter_upwards [hsupport] with z hz j hzevent
    exact hrawCover ⟨j.1, (Finset.mem_filter.mp j.2).1⟩ z
      ⟨hz.1, hpacket j.1 (hn j).1 (hn j).2.1 hzevent⟩
  obtain ⟨keep, hkeep, hbudget, hcap⟩ := F.exists_broad_physical_state_source hd hp
    (hp.residual_subset_event H₀ hHterminal) hHterminal old old hactive (fun j : I => j.1)
    (fun j => (hn j).1) (fun j => (hn j).2.1) hfraction hwidth0 hstrip he hret μ hμ
    (p.originalPhysicalCode (d.N k) old baseMesh hidden)
    (p.measurable_originalPhysicalCode (d.N k) old baseMesh hidden) menus ⌈K ^ 12⌉₊ hcard hcover hmenu
    δref hδ0 hδtop
  have hN : 0 < d.N k := (by norm_num : (0 : ℝ) < 2).trans_le (hd.1 k)
  have hsum : (∑ j : I, ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
      d.ν k (p.γ j.1) (p.A j.1)) ≤ ENNReal.ofReal (p.κ ^ 2) *
        (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) := by
    have hh := hp.local_reference_sum_le hN old stop good
      (fun b hb => (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2)
    calc
      _ = ∑ j : I, ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
          d.ν k (p.γ old) (p.A j.1) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [(hn j).2.1]
      _ = ∑ b ∈ good, ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ old) (p.A b) :=
        Finset.sum_coe_sort good (fun b => ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
          d.ν k (p.γ old) (p.A b))
      _ ≤ _ := hh
  refine ⟨keep, hkeep, hbudget.trans (add_le_add le_rfl ?_), hcap⟩
  have hh := mul_le_mul' (le_refl (δref * (⌈K ^ 12⌉₊ : ENNReal))) hsum
  simpa only [mul_assoc] using hh

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
