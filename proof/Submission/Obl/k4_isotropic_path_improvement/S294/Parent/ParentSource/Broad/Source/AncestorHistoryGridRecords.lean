-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorHistoryGridRecords, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AncestorHistoryGridRecords.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalDeepAncestorSignalMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentSignalCellCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.HistoryMenuRecords
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityNumerators

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open Submission.Lib.K4ListedExceptions
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
open scoped ENNReal

noncomputable section

/-- Literal joint support codes are the coordinate-grid codes of the
same unsheared base and same normalized ancestor signal. -/
theorem ancestor_joint_code_eq_coordinate_floors {W : ℕ}
    (N base hidden : ℝ) (p : PathData W) (root child : Fin p.C) (z : Ev) :
    jointCode base hidden (fun j => unshearedPacketBase p child z j)
      (physicalParentSignal N p child (p.R root) z)=
      fun j => ⌊parentUnshearedCoordinates N p child (p.R root) z j /
        ((Fin.snoc (fun _ : Fin 3 => base) hidden : Fin 4 → ℝ) j)⌋ := by
  ext j
  refine Fin.lastCases ?_ ?_ j
  · simp [jointCode,parentUnshearedCoordinates,Fin.snoc]
  · intro i
    simp [jointCode,parentUnshearedCoordinates,baseCode]

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

/-- Construct actual bounded records from the genuine earlier native
cores and actual retained palette histories. One finest grid is fixed
before every coarser query; no record, menu, diameter or cap oracle is
supplied. Original histories stay disjoint by their actual uniqueness. -/
theorem ValueBranchData.exists_ancestor_history_grid_records
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
    (E : Set Event) (hE : MeasurableSet E)
    (hECore : E⊆V.coreRetained cores (p.γ root)) :
    let coords := parentUnshearedCoordinates (d.N k) p child (p.R root);
    let referenceMesh : Fin 4 → ℝ := Fin.snoc (fun _ : Fin 3 => baseMesh) hidden;
    let Hist := fun deep : ↥(originalFinePackets p root stop) =>
      F.fineOriginalEvent root deep.1 univ;
    ∃ (n : ↥(originalFinePackets p root stop) → ℕ)
      (code : (v : ↥(originalFinePackets p root stop)) → Fin (n v) → (Fin 4 → ℤ))
      (piece : (Σ v, Fin (n v)) → Set Event),
      (∀ deep, (n deep:ℝ) ≤ K^12) ∧
      (∀ r, MeasurableSet (piece r)) ∧
      (∀ r, piece r⊆E∩Hist r.1) ∧
      Pairwise (fun r s => Disjoint (piece r) (piece s)) ∧
      (∀ z∈E, (∃ deep, z∈Hist deep) → ∃ r, z∈piece r) ∧
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
  obtain ⟨menus,hcard,hcover⟩ := V.exists_original_deep_ancestor_signal_menus
    Q hpure hd hp hHE hHbase hK hmax hpower hκK cores root child stop hmid hstop
    hr hrL hD hjets hwidth hbase hhidden hbaseSmall hcoreSmall hheightSmall
  have hlev (deep : ↥(originalFinePackets p root stop)) : p.lev deep.1=stop :=
    ((Finset.mem_filter.mp deep.2).2).1
  have hworld (deep : ↥(originalFinePackets p root stop)) : p.γ deep.1=p.γ root :=
    ((Finset.mem_filter.mp deep.2).2).2.1
  have hHist : ∀ deep, MeasurableSet (Hist deep) :=
    fun deep => F.fine_original_event_measurable hp root deep.1 hactive univ MeasurableSet.univ
  have hpacket (deep : ↥(originalFinePackets p root stop)) {z : Ev} (hz : z∈Hist deep) :
      z∈p.F deep.1 ∧ packetUnique p.lev p.γ p.F (p.γ root) z := by
    have hh : (z∈p.F deep.1 ∧ packetUnique p.lev p.γ p.F (p.γ root) z) ∧
        z∈p.terminalCoverage m (p.γ root) := by
      simpa only [PathData.packetWitness,ite_eq_left (And.intro (hlev deep) (hworld deep)),
        mem_inter_iff,mem_ofPred_eq] using hz.1
    exact hh.1
  have hdisj : Pairwise (fun v w => Disjoint (Hist v) (Hist w)) := by
    intro v w hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hv := hpacket v hz
    have hw := hpacket w hz'
    exact hne (Subtype.ext (hv.2 v.1 w.1 ((hlev v).trans (hlev w).symm)
      (hworld v) (hworld w) hv.1 hw.1))
  have hcoords : Measurable coords := measurable_parentUnshearedCoordinates _ _ _ _
  have href : ∀ j, 0 < referenceMesh j := by
    intro j
    refine Fin.lastCases ?_ (fun _ => ?_) j
    · simpa only [referenceMesh,Fin.snoc_last] using hhidden
    · simpa only [referenceMesh,Fin.snoc_castSucc] using hbase
  have hmenu : ∀ deep, ∀ z∈E∩Hist deep,
      (fun j => ⌊coords z j/referenceMesh j⌋)∈menus deep := by
    intro deep z hz
    change (fun j => ⌊parentUnshearedCoordinates (d.N k) p child (p.R root) z j /
      ((Fin.snoc (fun _ : Fin 3 => baseMesh) hidden : Fin 4 → ℝ) j)⌋)∈menus deep
    rw [←ancestor_joint_code_eq_coordinate_floors]
    exact hcover deep z ⟨hECore hz.1,(hpacket deep hz.2).1⟩
  obtain ⟨n,code,piece,hn,hm,hs,hpd,hpc,hqueries⟩ := exists_history_grid_records
    E hE Hist hHist hdisj coords hcoords referenceMesh href menus hmenu
  refine ⟨n,code,piece,?_,hm,hs,hpd,hpc,hqueries⟩
  intro deep
  rw [hn deep]
  exact hcard deep

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
