-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleRecordBlock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordGeometryInFamily
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordWindowRoom
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordAuxiliaryReferences
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeOriginalSourceBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRoot
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleScalars

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)

noncomputable section

/-- The complete geometry and reference part of the original record
block at one sample. The index is in the actual consecutive family;
the references fit both the MK4 graph and the auxiliary native queries. -/
theorem sample_record_geometry_block
    (tune : Tuning) {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {d₁ precision loss gain divisor τ graphMesh G : ℝ} {Ep i C : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hdepth : tune.depth κ₁ d₁ Ep precision loss=NativeDesign.depth κ₁ d₁ Ep precision loss)
    (hgain : 0 < gain) (hL : 0 < d.L) (hdivisor : 1 ≤ divisor)
    (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ gain/100) (htau : 0 ≤ τ)
    (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ)) (hs : ∀ j, s j=((j:ℝ)+1)/m)
    (hslack : censusSlack ≤ tune.slack)
    (hδtol : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain)
    (hC : windowOf tune κ₁ d₁ Ep precision loss gain*(m:ℝ) ≤ C)
    (hstop : i+C < m) (hib : i+childOffset κ₁ Ep precision gain m < m)
    (hKG : coreK p τ ≤ G) (hgeometry : d.N k^(2*δ₀*d.L) ≤ G)
    (hGpower : G ≤ d.N k^(recordGeometryExponent tune κ₁ d₁ Ep precision loss gain divisor*d.L))
    (hconstant : 24 ≤ d.N k^(gain*d.L))
    (hgraph0 : 0 < graphMesh) (hgraph1 : graphMesh ≤ 1)
    (hgraph : d.N k^(-(NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision*(gain*d.L))) ≤ graphMesh) :
    let c := childOffset κ₁ Ep precision gain m
    let nfam := C-familyMarginOf κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss gain) m+1
    let epsilon := epsOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (i+c)) (p.T i) (p.T (i+c))
    let chi := NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(gain*d.L)
    let finest : ℝ := NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss
    ∃ (jrec : Fin nfam) (baseRef hiddenRef : ℝ),
      0 < baseRef ∧ 0 < hiddenRef ∧ hiddenRef ≤ 1 ∧
      i+jrec.val ≤ i+C ∧ δ (d.N k) (p.r (i+jrec.val)) ≤ δ (d.N k) (p.r i) ∧
      (∀ root : Fin p.C, p.lev root=i → ∀ deep : Fin p.C, p.lev deep=i+C →
        p.unshearedDeepRadius root deep ≤ baseRef) ∧
      (∀ fine deep : Fin p.C, p.lev fine=i+jrec.val → p.lev deep=i+C →
        p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ ((coreK p τ)^FixedSourcePowers.coreRadius)⁻¹/12) ∧
      (∀ root : Fin p.C, p.lev root=i → ∀ fine deep : Fin p.C,
        p.lev fine=i+jrec.val → p.lev deep=i+C →
        (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev root)))*
          (2*((coreK p τ)^14*((coreK p τ)^6)⁻¹*
            (δ (d.N k) (p.r (i+jrec.val))/δ (d.N k) (p.r (p.lev root))))+
            (((coreK p τ)^(3*FixedSourcePowers.coreRadius+58+7))^FixedSourcePowers.jet*
              (p.κ+(coreK p τ)^14*((coreK p τ)^6)⁻¹))*
              (6*(coreK p τ)^FixedSourcePowers.coreRadius*p.deepBaseRadius (d.N k) d.L δ₀ fine deep)) ≤ hiddenRef) ∧
      3*baseRef ≤ graphMesh ∧ 3*hiddenRef ≤ graphMesh ∧
      3*baseRef ≤ (d.N k^chi)^(-finest) ∧ 3*hiddenRef ≤ (d.N k^chi)^(-finest) ∧
      3*((2:ℝ)^p.T (i+c)/(2:ℝ)^p.T i)*baseRef ≤ epsilon ∧
      3*(δ (d.N k) (p.r i)/δ (d.N k) (p.r (i+c)))*hiddenRef ≤ epsilon := by
  have hv0 := hv
  obtain ⟨_hd0,_hd1,hκ,hκ1,hprecision,hloss,hloss1⟩ := hv0
  have hN : 1 ≤ d.N k := (by norm_num : (1:ℝ) ≤ 2).trans (hd.1 k)
  have hNlt : 1 < d.N k := (by norm_num : (1:ℝ) < 2).trans_le (hd.1 k)
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  let c := childOffset κ₁ Ep precision gain m
  let g := familyMarginOf κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss gain) m
  let nfam := C-g+1
  let epsilon := epsOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (i+c)) (p.T i) (p.T (i+c))
  let chi := NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(gain*d.L)
  let finest : ℝ := NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss
  let referenceMesh := min graphMesh ((d.N k^chi)^(-finest))
  let baseRef := recordReference referenceMesh epsilon ((2:ℝ)^p.T i/(2:ℝ)^p.T (i+c))
  let hiddenRef := recordReference referenceMesh epsilon (δ (d.N k) (p.r (i+c))/δ (d.N k) (p.r i))
  have hepsilon : 0 < epsilon := by
    have hscalar := sample_scalars_pos (Ep:=Ep) (N:=d.N k) (L:=d.L) (precision:=precision)
      (loss:=loss) (gain:=gain) (rA:=p.r i) (rB:=p.r (i+c)) (TA:=p.T i) (TB:=p.T (i+c))
      hNlt (by positivity) (by have hp0 := zero_le_one.trans hprecision; positivity)
    exact hscalar.2.1
  obtain ⟨hbase,hhidden,hhidden1,hbg,hhg,hba,hha,hpb,hph⟩ :=
    original_auxiliary_record_reference_scales (graphMesh:=graphMesh) (epsilon:=epsilon)
      (chi:=chi) (finest:=finest) p i (i+c) hNp hgraph0 hepsilon hgraph1
  obtain ⟨hg,hwindow,hfamily⟩ := record_window_room tune hdepth hv hgain hδ0 hm hs hslack hδtol hδ hgm hC (i:=i)
  change g ≤ C at hg
  have hnfam : 0 < nfam := by dsimp only [nfam]; omega
  have hlevels (j : Fin nfam) : i+j.val < m := by
    have hj := j.isLt
    dsimp only [nfam] at hj
    omega
  have hi : i < m := by omega
  have hconstant6 : 6 ≤ d.N k^(gain*d.L) := by linarith only [hconstant]
  obtain ⟨hbaseFloor,hhiddenFloor⟩ := sample_native_record_reference_floors hp hv hN hL hgain hδ0 hδ
    hm hgm hs hi hib hconstant6 hgraph
  have hAccuracy := (native_record_accuracy_le_depth (Ep:=Ep) hv).1
  have hKbounds := Native.native_pre_geometry_envelope_bounds (source:=d.K k) hp.1 hN (add_nonneg htau htau)
  obtain ⟨j,hj,hwidth,hbaseSmall,hcoreSmall,hheightSmall⟩ := sample_record_geometry_in_family
    (d₁:=d₁) (precision:=precision) (Ep:=Ep) (divisor:=divisor)
    (accuracy:=nativeRecordAccuracyCoeff κ₁ d₁ Ep precision loss*gain)
    tune hd hp hκ hκ1 hL hloss hloss1 hgain hdivisor hδ0 hδ
    (mul_nonneg hAccuracy hgain.le) hm hgm hs hnfam hlevels hstop hwindow hfamily
    hKbounds.1 hKG hKbounds.2.2.1 hgeometry hGpower hconstant hbaseFloor hhiddenFloor hhidden1
  exact ⟨j,baseRef,hiddenRef,hbase,hhidden,hhidden1,hj,hwidth,hbaseSmall,hcoreSmall,hheightSmall,
    hbg,hhg,hba,hha,hpb,hph⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
