-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.BroadAncestorGridRecords, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorHistoryGridRecords
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RetainedAncestorHistories

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4ListedExceptions
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
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

/-- The actual broad residual supplies every retention-good fine
history used by the fixed-grid record family. Restricting the genuine
record partition to those unchanged histories preserves all source
points, costs no mass, and precedes EVERY later query grid. -/
theorem ValueBranchData.exists_broad_ancestor_history_grid_records
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
            (6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ fine deep)) ≤ hidden)
    (paletteMesh paletteBound : ℝ) (paletteFloor : ENNReal)
    (F : PaletteFamily Q (p.lev root) stop paletteMesh paletteBound paletteFloor)
    (hactive : F.active root)
    {broadRadius broadFraction : ℝ} (broad : BroadResidual F broadRadius broadFraction)
    (E : Set Event) (hE : MeasurableSet E)
    (hECore : E⊆V.coreRetained cores (p.γ root))
    (hEbroad : E⊆broad.residual (p.γ root)∩p.F root) :
    let coords := parentUnshearedCoordinates (d.N k) p child (p.R root);
    let referenceMesh : Fin 4 → ℝ := Fin.snoc (fun _ : Fin 3 => baseMesh) hidden;
    let Hist := fun deep : ↥(F.retainedOriginalFinePackets root) =>
      F.fineOriginalEvent root deep.1 univ;
    ∃ (n : ↥(F.retainedOriginalFinePackets root) → ℕ)
      (code : (v : ↥(F.retainedOriginalFinePackets root)) → Fin (n v) → (Fin 4 → ℤ))
      (piece : (Σ v, Fin (n v)) → Set Event),
      (∀ deep, (n deep:ℝ) ≤ K^12) ∧
      (∀ r, MeasurableSet (piece r)) ∧
      (∀ r, piece r⊆E∩Hist r.1) ∧
      Pairwise (fun r s => Disjoint (piece r) (piece s)) ∧
      (∀ z∈E, ∃ r, z∈piece r) ∧
      ∀ queryMesh : Fin 4 → ℝ, (∀ j, 0 < queryMesh j) →
        (∀ j, referenceMesh j ≤ queryMesh j) → ∀ r,
          (referenceCellOptions referenceMesh queryMesh (code r.1 r.2)).card=81 ∧
          (∀ z∈piece r, (fun j => ⌊coords z j/queryMesh j⌋)∈
            referenceCellOptions referenceMesh queryMesh (code r.1 r.2)) ∧
          ∀ q∈referenceCellOptions referenceMesh queryMesh (code r.1 r.2),
            (integerCodeBox 2 q).card=625 ∧
            ∀ z∈piece r, (fun j => ⌊coords z j/queryMesh j⌋)∈integerCodeBox 2 q := by
  intro coords referenceMesh Hist
  classical
  obtain ⟨n,code,piece,hn,hm,hs,hdj,hcover,hqueries⟩ := V.exists_ancestor_history_grid_records
    Q hpure hd hp hHE hHbase hK hmax hpower hκK cores root child stop hmid hstop
    hr hrL hD hjets hwidth hbase hhidden hbaseSmall hcoreSmall hheightSmall
    paletteMesh paletteBound paletteFloor F hactive E hE hECore
  let embed : ↥(F.retainedOriginalFinePackets root) → ↥(originalFinePackets p root stop) :=
    fun deep => ⟨deep.1,(F.retained_original_fine_spec root deep).1⟩
  let nGood := fun deep : ↥(F.retainedOriginalFinePackets root) => n (embed deep)
  let codeGood := fun (deep : ↥(F.retainedOriginalFinePackets root))
    (j : Fin (nGood deep)) => code (embed deep) j
  let record : (Σ deep, Fin (nGood deep)) → (Σ deep, Fin (n deep)) :=
    fun r => ⟨embed r.1,r.2⟩
  let pieceGood := fun r : Σ deep, Fin (nGood deep) => piece (record r)
  have hrecord : Function.Injective record := by
    rintro ⟨v,j⟩ ⟨w,l⟩ heq
    have hvw : v=w := Subtype.ext (congrArg (fun r => r.1.1) heq)
    subst w
    have hjl : j=l := eq_of_heq (Sigma.mk.inj heq).2
    subst l
    rfl
  refine ⟨nGood,codeGood,pieceGood,?_,?_,?_,?_,?_,?_⟩
  · intro deep
    exact hn (embed deep)
  · intro r
    exact hm (record r)
  · intro r
    exact hs (record r)
  · intro r s hne
    exact hdj (fun heq => hne (hrecord heq))
  · intro z hz
    have hio : p.lev root ≤ stop := hmid.trans hstop
    obtain ⟨good,hgood⟩ := Native.BroadResidual.exists_retained_original_fine_history F broad hp hio root rfl z (hEbroad hz)
    obtain ⟨r,hr⟩ := hcover z hz ⟨embed good,hgood⟩
    have hret := Native.BroadResidual.retention_good_of_fine_original_event F broad hp hio root rfl r.1
      z (hEbroad hz) (hs r hr).2
    let goodr : ↥(F.retainedOriginalFinePackets root) :=
      ⟨r.1.1,Finset.mem_filter.mpr ⟨r.1.2,hret⟩⟩
    refine ⟨⟨goodr,r.2⟩,?_⟩
    exact hr
  · intro queryMesh hquery hsize r
    exact hqueries queryMesh hquery hsize (record r)

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
