-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Clauses
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorRecordNaturalStates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorRelativeCodes
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalPaletteVector

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily velocityPalette labelledVelocityPalette)
open Parent.OriginalVelocityPalette
open Submission.Lib.K4ListedExceptions
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- The actual retained ancestor records give the relative row packet's
state clauses on any later source. The same natural states read the
ancestor graph rows and globally refine the effective physical code.
Both strip breadth and the original velocity palette pass through one
bounded-option fraction keep. -/
theorem record_states_of_ancestor_source_with_record_ratios
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root child : Fin p.C) (hactive : F.active root)
    (n : ↥(F.retainedOriginalFinePackets root) → ℕ)
    (code : (deep : ↥(F.retainedOriginalFinePackets root)) → Fin (n deep) → (Fin 4 → ℤ))
    (piece : (Σ deep, Fin (n deep)) → Set Ev)
    (hm : ∀ r, MeasurableSet (piece r))
    (hdj : Pairwise (fun r s => Disjoint (piece r) (piece s)))
    (hsub : ∀ r, piece r⊆F.fineOriginalEvent root r.1.1 univ)
    {frontRadius fraction : ℝ} (hfr : 0 ≤ fraction)
    (hwide : ∀ r, (piece r).Nonempty → F.coding.code r.1.1∉
      Q.intrinsicNarrowStates F.code stop F.U frontRadius fraction root)
    (reservoir : Set Ev) (hreservoir : MeasurableSet reservoir)
    (hcover : ∀ z∈reservoir, ∃ r, z∈piece r)
    (cut : ℝ) (hcut : 0 < cut)
    (hfloor : ∀ r, (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece r)=0 ∨
      ENNReal.ofReal cut*((d.ν k (p.γ root)).prod volume)
        (F.fineOriginalEvent root r.1.1 univ) ≤
          (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece r))
    (pv paletteRatio : ℝ)
    (hpalette : ∀ rec (D : Set (ℤ×ℤ)), MeasurableSet D →
      (((d.ν k (p.γ root)).prod volume).restrict reservoir)
        {z | z∈piece rec ∧ velocityPalette pv (Parent.v z.1)∈D} ≤
          ENNReal.ofReal ((8*paletteRatio)/cut)*
            (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece rec)*
              ((Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette pv)) D)
    {baseRef hiddenRef graphMesh eps aEff : ℝ}
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef)
    (hgraphMesh : 0 < graphMesh) (heps : 0 < eps) (haEff : 0 < aEff)
    (hrecords : ∀ r z, z∈piece r →
      (fun j => ⌊parentUnshearedCoordinates (d.N k) p root (p.R root) z j /
        ((Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef : Fin 4 → ℝ) j)⌋)∈
      referenceCellOptions
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef)
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef) (code r.1 r.2))
    (hgraphBase : 3*baseRef ≤ graphMesh) (hgraphHidden : 3*hiddenRef ≤ graphMesh)
    (hphysicalBase : 3*((2:ℝ)^p.T (p.lev child)/(2:ℝ)^p.T (p.lev root))*baseRef ≤ eps)
    (hphysicalHidden : 3*(δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*hiddenRef ≤
      (aEff/δ (d.N k) (p.r (p.lev child)))*eps)
    (S : Set Ev) (hS : MeasurableSet S) (hSsub : S⊆reservoir)
    (beta : ENNReal) (hbeta : beta≠0) (hbetaTop : beta≠⊤)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) {bound K : ℝ} (hbound : 0 ≤ bound)
    (hrow : ∀ q j, |row q j| ≤ bound)
    (hstripWidth : K^(-100:ℝ)*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q root j l|) ≤
      frontRadius*((2:ℝ)^p.T (p.lev root)*|(p.Q root).det|))
    (hstripRatio : ENNReal.ofReal ((8*fraction)/cut)/beta ≤ (1/2000000000000:ENNReal))
    (hpaletteRatio : ENNReal.ofReal ((8*paletteRatio)/cut)/beta ≤ ENNReal.ofReal K) :
    ∃ (keep : Set Ev) (state : Ev → ℕ) (value : ℕ → Fin 3 → ℝ),
      keep⊆S ∧
      ((d.ν k (p.γ root)).prod volume) S ≤ ((d.ν k (p.γ root)).prod volume) keep+
        (6561:ENNReal)*beta*((d.ν k (p.γ root)).prod volume) reservoir ∧
      StateClauses K eps pv (d.ν k (p.γ root)) (unshearedPacketBase p child)
        (fun z => MvPolynomial.eval (xp z.1 z.2) (p.R root)/aEff) keep state
        (originalVectorPalette F root pv) ∧
      (∀ z, value (state z)=row (clockParentCode p root
        (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh z)) ∧
      (∀ j c, |value j c| ≤ bound) ∧
      (∀ x y, state x=state y →
        clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh x=
        clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh y) ∧
      (∀ (B : Set Ev) (cap : ENNReal),
        (∀ rec, (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece rec∩B) ≤
          cap*(((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece rec)) →
        ∀ j, (((d.ν k (p.γ root)).prod volume).restrict keep)
          {z | state z=j ∧ z∈B} ≤
            (cap/beta)*(((d.ν k (p.γ root)).prod volume).restrict keep) {z | state z=j}) ∧
      ∀ (B : Set Ev) (cap : ENNReal),
        (∀ rec, (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece rec∩B) ≤
          cap*(((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece rec)) →
        ∀ label, (((d.ν k (p.γ root)).prod volume).restrict keep)
          {z | clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root)
            graphMesh z=label ∧ z∈B} ≤
            (cap/beta)*(((d.ν k (p.γ root)).prod volume).restrict keep)
              {z | clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root)
                graphMesh z=label} := by
  classical
  let Rec := Σ deep : ↥(F.retainedOriginalFinePackets root), Fin (n deep)
  letI : MeasurableSpace Rec := ⊤
  letI : MeasurableSingletonClass Rec := ⟨fun _ => trivial⟩
  let raw := (d.ν k (p.γ root)).prod (volume : Measure ℝ)
  let μ := raw.restrict reservoir
  let piPair := (Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette pv)
  have hcoverage : ∀ᵐ z ∂μ, ∃ rec, z∈piece rec := by
    filter_upwards [ae_restrict_mem hreservoir] with z hz
    exact hcover z hz
  have hclock : (2:ℝ)^p.T (p.lev root)≠0 := by positivity
  have hrootScale : δ (d.N k) (p.r (p.lev root))≠0 := by unfold δ; positivity
  have hchildScale : 0 < δ (d.N k) (p.r (p.lev child)) := by unfold δ; positivity
  obtain ⟨keep,state,value,hkeep,hkeepSub,hstate,hfinite,hloss,hfaith,hvalue,hvalueBound,
      hcodes,hratios⟩ := ancestor_record_query_natural_states (Rec := Rec) (d.N k) root root child
    piece (fun rec => code rec.1 rec.2) hm hdj μ hcoverage hbaseRef hhiddenRef
    hgraphMesh hgraphMesh heps (by positivity) hrecords
    (by simpa only [div_self hclock,mul_one] using hgraphBase)
    (by simpa only [div_self hrootScale,mul_one] using hgraphHidden)
    hphysicalBase hphysicalHidden S hS (fun z hz => hcover z (hSsub hz))
    beta hbeta hbetaTop row hbound hrow
  have hkeepReservoir : keep⊆reservoir := hkeepSub.trans hSsub
  have hrawLoss : raw (S\keep) ≤ (6561:ENNReal)*beta*raw reservoir := by
    simpa only [μ,Measure.restrict_eq_self raw
      (show S\keep⊆reservoir from fun z hz => hSsub hz.1),
      Measure.restrict_apply_univ,Nat.cast_ofNat] using hloss
  have hstateRatio (B : Set Ev) (cap : ENNReal)
      (hcap : ∀ rec : Rec, μ (piece rec∩B) ≤ cap*μ (piece rec)) (j : ℕ) :
      (raw.restrict keep) {z | state z=j ∧ z∈B} ≤
        (cap/beta)*(raw.restrict keep) {z | state z=j} := by
    have h := hratios B cap hcap j
    have hnum : (keep∩state ⁻¹' {j})∩B={z | state z=j ∧ z∈B}∩keep := by
      ext z
      simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
      tauto
    have hden : keep∩state ⁻¹' {j}={z | state z=j}∩keep := by
      ext z
      simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
      tauto
    dsimp only [μ] at h
    rw [hnum,hden,←Measure.restrict_apply' hkeep,←Measure.restrict_apply' hkeep,
      Measure.restrict_restrict_of_subset hkeepReservoir] at h
    exact h
  have hf (deep : ↥(F.retainedOriginalFinePackets root)) : p.lev deep.1=stop :=
    (Finset.mem_filter.mp (F.retained_original_fine_spec root deep).1).2.1
  have hw (deep : ↥(F.retainedOriginalFinePackets root)) : p.γ deep.1=p.γ root :=
    (Finset.mem_filter.mp (F.retained_original_fine_spec root deep).1).2.2.1
  refine ⟨keep,state,value,hkeepSub,?_,?_,?_,hvalueBound,?_,hstateRatio,?_⟩
  · calc
      raw S = raw keep+raw (S\keep) := by
        rw [←measure_inter_add_sdiff S hkeep,inter_eq_right.mpr hkeepSub]
      _ ≤ raw keep+(6561:ENNReal)*beta*raw reservoir := add_le_add_right hrawLoss _
  · refine ⟨hkeep,hstate,hfinite,?_,?_,originalVectorPalette_probability F hd hp hHE root hactive pv,?_⟩
    · intro z z' hzz'
      exact physical_code_eq_of_ancestor_joint_eq (d.N k) p root child haEff heps z z'
        (hfaith z z' hzz').2
    · intro j normal offset hnormal
      have hc := hstateRatio {z | |Inner.inner ℝ normal (Parent.v z.1)-offset| ≤ K^(-100:ℝ)}
        (ENNReal.ofReal ((8*fraction)/cut)) (fun rec => ?_) j
      · exact hc.trans (mul_le_mul' hstripRatio le_rfl)
      · by_cases hne : (piece rec).Nonempty
        · exact F.current_record_physical_strip_cap hd hp hHE hH root rec.1.1 hactive
            (hf rec.1) (hw rec.1) hfr (hwide rec hne)
            (F.retained_original_fine_spec root rec.1).2 μ Measure.restrict_le_self
            (piece rec) (hsub rec) cut hcut (hfloor rec) normal hnormal offset hstripWidth
        · have hempty : piece rec=∅ := Set.not_nonempty_iff_eq_empty.mp hne
          apply (measure_mono inter_subset_left).trans
          simp only [hempty,measure_empty,mul_zero,le_refl]
    · intro j b
      apply vector_palette_guarded_cap (raw.restrict keep) piPair pv
        (fun z i => Parent.v z.1 i) {z | state z=j}
        (ENNReal.ofReal K*(raw.restrict keep) {z | state z=j}) ?_ b
      intro D hD
      have hc := hstateRatio {z | velocityPalette pv (Parent.v z.1)∈D}
        (ENNReal.ofReal ((8*paletteRatio)/cut)*piPair D) (fun rec => ?_) j
      · calc
          _ ≤ ((ENNReal.ofReal ((8*paletteRatio)/cut)*piPair D)/beta)*
              (raw.restrict keep) {z | state z=j} := hc
          _ = (ENNReal.ofReal ((8*paletteRatio)/cut)/beta)*
              (raw.restrict keep) {z | state z=j}*piPair D := by
            simp only [div_eq_mul_inv]
            ac_rfl
          _ ≤ ENNReal.ofReal K*(raw.restrict keep) {z | state z=j}*piPair D :=
            mul_le_mul' (mul_le_mul' hpaletteRatio le_rfl) le_rfl
      · have heq : piece rec∩{z | velocityPalette pv (Parent.v z.1)∈D}=
            {z | z∈piece rec ∧ velocityPalette pv (Parent.v z.1)∈D} := by
          ext z
          simp only [mem_inter_iff,mem_ofPred_eq]
        rw [heq]
        simpa only [μ,raw,piPair,mul_assoc,mul_comm,mul_left_comm] using hpalette rec D hD
  · intro z
    simpa only [ancestor_root_joint_eq_clock_code] using hvalue z
  · intro x y hxy
    simpa only [ancestor_root_joint_eq_clock_code] using (hfaith x y hxy).1
  · intro B cap hcap label
    have h := (hcodes B cap hcap).1 label
    simp only [ancestor_root_joint_eq_clock_code] at h
    let graphCode := clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh
    have hnum : (keep∩graphCode ⁻¹' {label})∩B={z | graphCode z=label ∧ z∈B}∩keep := by
      ext z
      simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
      tauto
    have hden : keep∩graphCode ⁻¹' {label}={z | graphCode z=label}∩keep := by
      ext z
      simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
      tauto
    change μ ((keep∩graphCode ⁻¹' {label})∩B) ≤ (cap/beta)*μ (keep∩graphCode ⁻¹' {label}) at h
    dsimp only [μ] at h
    rw [hnum,hden,←Measure.restrict_apply' hkeep,←Measure.restrict_apply' hkeep,
      Measure.restrict_restrict_of_subset hkeepReservoir] at h
    exact h

/-- The graph-faithful interface retains its existing output shape. -/
theorem record_states_of_ancestor_source_with_graph_code
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root child : Fin p.C) (hactive : F.active root)
    (n : ↥(F.retainedOriginalFinePackets root) → ℕ)
    (code : (deep : ↥(F.retainedOriginalFinePackets root)) → Fin (n deep) → (Fin 4 → ℤ))
    (piece : (Σ deep, Fin (n deep)) → Set Ev)
    (hm : ∀ r, MeasurableSet (piece r))
    (hdj : Pairwise (fun r s => Disjoint (piece r) (piece s)))
    (hsub : ∀ r, piece r⊆F.fineOriginalEvent root r.1.1 univ)
    {frontRadius fraction : ℝ} (hfr : 0 ≤ fraction)
    (hwide : ∀ r, (piece r).Nonempty → F.coding.code r.1.1∉
      Q.intrinsicNarrowStates F.code stop F.U frontRadius fraction root)
    (reservoir : Set Ev) (hreservoir : MeasurableSet reservoir)
    (hcover : ∀ z∈reservoir, ∃ r, z∈piece r)
    (cut : ℝ) (hcut : 0 < cut)
    (hfloor : ∀ r, (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece r)=0 ∨
      ENNReal.ofReal cut*((d.ν k (p.γ root)).prod volume)
        (F.fineOriginalEvent root r.1.1 univ) ≤
          (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece r))
    (pv paletteRatio : ℝ)
    (hpalette : ∀ rec (D : Set (ℤ×ℤ)), MeasurableSet D →
      (((d.ν k (p.γ root)).prod volume).restrict reservoir)
        {z | z∈piece rec ∧ velocityPalette pv (Parent.v z.1)∈D} ≤
          ENNReal.ofReal ((8*paletteRatio)/cut)*
            (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece rec)*
              ((Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette pv)) D)
    {baseRef hiddenRef graphMesh eps aEff : ℝ}
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef)
    (hgraphMesh : 0 < graphMesh) (heps : 0 < eps) (haEff : 0 < aEff)
    (hrecords : ∀ r z, z∈piece r →
      (fun j => ⌊parentUnshearedCoordinates (d.N k) p root (p.R root) z j /
        ((Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef : Fin 4 → ℝ) j)⌋)∈
      referenceCellOptions
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef)
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef) (code r.1 r.2))
    (hgraphBase : 3*baseRef ≤ graphMesh) (hgraphHidden : 3*hiddenRef ≤ graphMesh)
    (hphysicalBase : 3*((2:ℝ)^p.T (p.lev child)/(2:ℝ)^p.T (p.lev root))*baseRef ≤ eps)
    (hphysicalHidden : 3*(δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*hiddenRef ≤
      (aEff/δ (d.N k) (p.r (p.lev child)))*eps)
    (S : Set Ev) (hS : MeasurableSet S) (hSsub : S⊆reservoir)
    (beta : ENNReal) (hbeta : beta≠0) (hbetaTop : beta≠⊤)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) {bound K : ℝ} (hbound : 0 ≤ bound)
    (hrow : ∀ q j, |row q j| ≤ bound)
    (hstripWidth : K^(-100:ℝ)*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q root j l|) ≤
      frontRadius*((2:ℝ)^p.T (p.lev root)*|(p.Q root).det|))
    (hstripRatio : ENNReal.ofReal ((8*fraction)/cut)/beta ≤ (1/2000000000000:ENNReal))
    (hpaletteRatio : ENNReal.ofReal ((8*paletteRatio)/cut)/beta ≤ ENNReal.ofReal K) :
    ∃ (keep : Set Ev) (state : Ev → ℕ) (value : ℕ → Fin 3 → ℝ),
      keep⊆S ∧
      ((d.ν k (p.γ root)).prod volume) S ≤ ((d.ν k (p.γ root)).prod volume) keep+
        (6561:ENNReal)*beta*((d.ν k (p.γ root)).prod volume) reservoir ∧
      StateClauses K eps pv (d.ν k (p.γ root)) (unshearedPacketBase p child)
        (fun z => MvPolynomial.eval (xp z.1 z.2) (p.R root)/aEff) keep state
        (originalVectorPalette F root pv) ∧
      (∀ z, value (state z)=row (clockParentCode p root
        (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh z)) ∧
      (∀ j c, |value j c| ≤ bound) ∧
      ∀ x y, state x=state y →
        clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh x=
        clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh y := by
  obtain ⟨keep,state,value,hkeep,hloss,hstates,hvalue,hbound',hgraph,_hstateRatios,_hgraphRatios⟩ :=
    record_states_of_ancestor_source_with_record_ratios F hd hp hHE hH root child hactive n code piece
      hm hdj hsub hfr hwide reservoir hreservoir hcover cut hcut hfloor pv paletteRatio hpalette
      hbaseRef hhiddenRef hgraphMesh heps haEff hrecords hgraphBase hgraphHidden
      hphysicalBase hphysicalHidden S hS hSsub beta hbeta hbetaTop row hbound hrow
      hstripWidth hstripRatio hpaletteRatio
  exact ⟨keep,state,value,hkeep,hloss,hstates,hvalue,hbound',hgraph⟩

/-- The original record-state interface, retaining its existing output shape. -/
theorem record_states_of_ancestor_source
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root child : Fin p.C) (hactive : F.active root)
    (n : ↥(F.retainedOriginalFinePackets root) → ℕ)
    (code : (deep : ↥(F.retainedOriginalFinePackets root)) → Fin (n deep) → (Fin 4 → ℤ))
    (piece : (Σ deep, Fin (n deep)) → Set Ev)
    (hm : ∀ r, MeasurableSet (piece r))
    (hdj : Pairwise (fun r s => Disjoint (piece r) (piece s)))
    (hsub : ∀ r, piece r⊆F.fineOriginalEvent root r.1.1 univ)
    {frontRadius fraction : ℝ} (hfr : 0 ≤ fraction)
    (hwide : ∀ r, (piece r).Nonempty → F.coding.code r.1.1∉
      Q.intrinsicNarrowStates F.code stop F.U frontRadius fraction root)
    (reservoir : Set Ev) (hreservoir : MeasurableSet reservoir)
    (hcover : ∀ z∈reservoir, ∃ r, z∈piece r)
    (cut : ℝ) (hcut : 0 < cut)
    (hfloor : ∀ r, (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece r)=0 ∨
      ENNReal.ofReal cut*((d.ν k (p.γ root)).prod volume)
        (F.fineOriginalEvent root r.1.1 univ) ≤
          (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece r))
    (pv paletteRatio : ℝ)
    (hpalette : ∀ rec (D : Set (ℤ×ℤ)), MeasurableSet D →
      (((d.ν k (p.γ root)).prod volume).restrict reservoir)
        {z | z∈piece rec ∧ velocityPalette pv (Parent.v z.1)∈D} ≤
          ENNReal.ofReal ((8*paletteRatio)/cut)*
            (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece rec)*
              ((Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette pv)) D)
    {baseRef hiddenRef graphMesh eps aEff : ℝ}
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef)
    (hgraphMesh : 0 < graphMesh) (heps : 0 < eps) (haEff : 0 < aEff)
    (hrecords : ∀ r z, z∈piece r →
      (fun j => ⌊parentUnshearedCoordinates (d.N k) p root (p.R root) z j /
        ((Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef : Fin 4 → ℝ) j)⌋)∈
      referenceCellOptions
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef)
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef) (code r.1 r.2))
    (hgraphBase : 3*baseRef ≤ graphMesh) (hgraphHidden : 3*hiddenRef ≤ graphMesh)
    (hphysicalBase : 3*((2:ℝ)^p.T (p.lev child)/(2:ℝ)^p.T (p.lev root))*baseRef ≤ eps)
    (hphysicalHidden : 3*(δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*hiddenRef ≤
      (aEff/δ (d.N k) (p.r (p.lev child)))*eps)
    (S : Set Ev) (hS : MeasurableSet S) (hSsub : S⊆reservoir)
    (beta : ENNReal) (hbeta : beta≠0) (hbetaTop : beta≠⊤)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) {bound K : ℝ} (hbound : 0 ≤ bound)
    (hrow : ∀ q j, |row q j| ≤ bound)
    (hstripWidth : K^(-100:ℝ)*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q root j l|) ≤
      frontRadius*((2:ℝ)^p.T (p.lev root)*|(p.Q root).det|))
    (hstripRatio : ENNReal.ofReal ((8*fraction)/cut)/beta ≤ (1/2000000000000:ENNReal))
    (hpaletteRatio : ENNReal.ofReal ((8*paletteRatio)/cut)/beta ≤ ENNReal.ofReal K) :
    ∃ (keep : Set Ev) (state : Ev → ℕ) (value : ℕ → Fin 3 → ℝ),
      keep⊆S ∧
      ((d.ν k (p.γ root)).prod volume) S ≤ ((d.ν k (p.γ root)).prod volume) keep+
        (6561:ENNReal)*beta*((d.ν k (p.γ root)).prod volume) reservoir ∧
      StateClauses K eps pv (d.ν k (p.γ root)) (unshearedPacketBase p child)
        (fun z => MvPolynomial.eval (xp z.1 z.2) (p.R root)/aEff) keep state
        (originalVectorPalette F root pv) ∧
      (∀ z, value (state z)=row (clockParentCode p root
        (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh z)) ∧
      ∀ j c, |value j c| ≤ bound := by
  obtain ⟨keep,state,value,hkeep,hloss,hstates,hvalue,hbound',_hgraph⟩ :=
    record_states_of_ancestor_source_with_graph_code F hd hp hHE hH root child hactive n code piece
      hm hdj hsub hfr hwide reservoir hreservoir hcover cut hcut hfloor pv paletteRatio hpalette
      hbaseRef hhiddenRef hgraphMesh heps haEff hrecords hgraphBase hgraphHidden
      hphysicalBase hphysicalHidden S hS hSsub beta hbeta hbetaTop row hbound hrow
      hstripWidth hstripRatio hpaletteRatio
  exact ⟨keep,state,value,hkeep,hloss,hstates,hvalue,hbound'⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
