-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.AncestorRecordRatioStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.CoarsenedStatePalette
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AllAncestorRecordSources
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorRecordChildLocalization

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily velocityPalette labelledVelocityPalette)
open Parent.OriginalVelocityPalette
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ}
    {root : Fin p.C} {E : Set Ev}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension Kcap : ℝ}
    (data : OriginalAncestorRecordSource F root E Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap)
    (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- The coherent original ancestor source transfers EVERY conditional
record event ratio onto BOTH final natural states and graph-code fibers.
It uses the same single keep and original probability palette as the
state clauses; wider strip bounds require no additional restriction. -/
theorem OriginalAncestorRecordSource.relative_states_with_record_ratios
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hactive : F.active root) (hEbase : E⊆Q.base (p.γ root))
    (child : Fin p.C) (hworld : p.γ child=p.γ root) (hchild : p.lev child ≤ stop)
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hcut : 0 < cut) (hfr : 0 ≤ fraction)
    {graphMesh eps aEff pv K : ℝ} (hgraph : 0 < graphMesh) (heps : 0 < eps) (haEff : 0 < aEff)
    (hfinePv : 0 < finePv) (hpv : finePv ≤ pv) (hK : 0 < K)
    (hgraphBase : 3*baseRef ≤ graphMesh) (hgraphHidden : 3*hiddenRef ≤ graphMesh)
    (hphysicalBase : 3*((2:ℝ)^p.T (p.lev child)/(2:ℝ)^p.T (p.lev root))*baseRef ≤ eps)
    (hphysicalHidden : 3*(δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*hiddenRef ≤
      (aEff/δ (d.N k) (p.r (p.lev child)))*eps)
    (S : Set Ev) (hS : MeasurableSet S) (hSsub : S⊆data.kept∩p.F child)
    (beta : ENNReal) (hbeta : beta≠0) (hbetaTop : beta≠⊤)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) {bound : ℝ} (hbound : 0 ≤ bound)
    (hrow : ∀ q j, |row q j| ≤ bound)
    (hstripWidth : (K/4)^(-100:ℝ)*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q root j l|) ≤
      frontRadius*((2:ℝ)^p.T (p.lev root)*|(p.Q root).det|))
    (hstripRatio : ENNReal.ofReal ((8*fraction)/cut)/beta ≤ (1/2000000000000:ENNReal))
    (hpaletteRatio : ENNReal.ofReal ((8*paletteRatio)/cut)/beta ≤ ENNReal.ofReal (K/4)) :
    ∃ (keep : Set Ev) (state : Ev → ℕ) (value : ℕ → Fin 3 → ℝ) (palette : Measure (Fin 2 → ℤ)),
      keep⊆S ∧
      ((d.ν k (p.γ root)).prod volume) S ≤ ((d.ν k (p.γ root)).prod volume) keep+
        (6561:ENNReal)*beta*(d.ν k (p.γ child) (p.A child)*
          ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹)) ∧
      StateClauses K eps pv (d.ν k (p.γ root)) (unshearedPacketBase p child)
        (fun z => MvPolynomial.eval (xp z.1 z.2) (p.R root)/aEff) keep state palette ∧
      (∀ z, value (state z)=row (clockParentCode p root
        (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh z)) ∧
      (∀ j c, |value j c| ≤ bound) ∧
      (∀ x y, state x=state y →
        clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh x=
        clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh y) ∧
      (∀ (B : Set Ev) (cap : ENNReal),
        (∀ rec, (((d.ν k (p.γ root)).prod volume).restrict (data.kept∩p.F child))
          (data.piece rec∩B) ≤ cap*(((d.ν k (p.γ root)).prod volume).restrict
            (data.kept∩p.F child)) (data.piece rec)) →
        ∀ j, (((d.ν k (p.γ root)).prod volume).restrict keep) {z | state z=j ∧ z∈B} ≤
          (cap/beta)*(((d.ν k (p.γ root)).prod volume).restrict keep) {z | state z=j}) ∧
      ∀ (B : Set Ev) (cap : ENNReal),
        (∀ rec, (((d.ν k (p.γ root)).prod volume).restrict (data.kept∩p.F child))
          (data.piece rec∩B) ≤ cap*(((d.ν k (p.γ root)).prod volume).restrict
            (data.kept∩p.F child)) (data.piece rec)) →
        ∀ label, (((d.ν k (p.γ root)).prod volume).restrict keep)
          {z | clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root)
            graphMesh z=label ∧ z∈B} ≤
          (cap/beta)*(((d.ν k (p.γ root)).prod volume).restrict keep)
            {z | clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root)
              graphMesh z=label} := by
  classical
  let raw := (d.ν k (p.γ root)).prod (volume : Measure ℝ)
  let μ := raw.restrict data.kept
  let reservoir := data.kept∩p.F child
  have hmChild : MeasurableSet (p.F child) :=
    (hp.2.2.2.2.2.2.2 child).2.2.2.2.2.2.2.2.2.1
  have hmRes : MeasurableSet reservoir := data.kept_measurable.inter hmChild
  have hloc := F.record_child_localization hp root child hworld hchild
    (fun rec => rec.1) data.piece (fun rec z hz => (data.subset rec hz).2)
    (fun rec z hz => hEbase (data.subset rec hz).1)
  obtain ⟨hfloorChild,hratios⟩ := hloc.2 μ
    (fun rec => ENNReal.ofReal cut*raw (F.fineOriginalEvent root rec.1.1 univ)) data.floor
  have hlaw : μ.restrict (p.F child)=raw.restrict reservoir := by
    change (raw.restrict data.kept).restrict (p.F child)=raw.restrict (data.kept∩p.F child)
    rw [Measure.restrict_restrict hmChild,inter_comm]
  have hfloor : ∀ rec, (raw.restrict reservoir) (data.piece rec)=0 ∨
      ENNReal.ofReal cut*raw (F.fineOriginalEvent root rec.1.1 univ) ≤
        (raw.restrict reservoir) (data.piece rec) := by
    simpa only [hlaw] using hfloorChild
  have hpalette (rec) (D : Set (ℤ×ℤ)) (hD : MeasurableSet D) :
      (raw.restrict reservoir) {z | z∈data.piece rec ∧ velocityPalette finePv (Parent.v z.1)∈D} ≤
        ENNReal.ofReal ((8*paletteRatio)/cut)*(raw.restrict reservoir) (data.piece rec)*
          ((Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette finePv)) D := by
    have hset (rec) : data.piece rec∩{z | velocityPalette finePv (Parent.v z.1)∈D}=
        {z | z∈data.piece rec ∧ velocityPalette finePv (Parent.v z.1)∈D} := by
      ext z
      simp only [mem_inter_iff,mem_ofPred_eq]
    have hcap (rec) : μ (data.piece rec∩{z | velocityPalette finePv (Parent.v z.1)∈D}) ≤
        (ENNReal.ofReal ((8*paletteRatio)/cut)*
          ((Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette finePv)) D)*
            μ (data.piece rec) := by
      rw [hset rec]
      simpa only [mul_assoc,mul_comm,mul_left_comm,Parent.v,Parent.ParentSource.v] using
        data.palette rec D hD
    have hc := hratios {z | velocityPalette finePv (Parent.v z.1)∈D} _ hcap rec
    rw [hlaw,hset rec] at hc
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hc
  obtain ⟨keep,state,value,hkeepSub,hloss,hstates,hvalue,hvalueBound,hgraphFaith,hstateRatios,hgraphRatios⟩ :=
    record_states_of_ancestor_source_with_record_ratios F hd hp hHE hH root child hactive data.n data.code data.piece
      data.measurable data.disjoint (fun rec z hz => (data.subset rec hz).2) hfr data.wide
      reservoir hmRes (fun z hz => data.cover z (data.kept_subset hz.1)) cut hcut hfloor
      finePv paletteRatio hpalette hbaseRef hhiddenRef hgraph heps haEff data.localization
      hgraphBase hgraphHidden hphysicalBase hphysicalHidden S hS hSsub beta hbeta hbetaTop
      row hbound hrow hstripWidth hstripRatio hpaletteRatio
  obtain ⟨palette,hcoarse⟩ := hstates.coarsen_palette (by positivity : 0 < K/4)
    (by linarith : 4*(K/4) ≤ K) hfinePv hpv
  have hreference : raw reservoir ≤ d.ν k (p.γ child) (p.A child)*
      ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹) := by
    calc
      _ ≤ raw (p.fullCylinder child) := measure_mono
        (fun _ hz => hp.counted_subset_fullCylinder child hz.2)
      _ = _ := by
        simpa only [raw,hworld] using p.fullCylinder_mass (d.ν k (p.γ root)) child
  refine ⟨keep,state,value,palette,hkeepSub,?_,hcoarse,hvalue,hvalueBound,hgraphFaith,
    hstateRatios,hgraphRatios⟩
  exact hloss.trans (add_le_add_right (mul_le_mul' le_rfl hreference) _)

/-- Actual retained histories and their full-original floors supply
original-velocity strips of ANY resolved width on each child reservoir.
The bound is separate from the final state's palette constant K. -/
theorem OriginalAncestorRecordSource.child_record_original_strip_cap
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hactive : F.active root) (hEbase : E⊆Q.base (p.γ root))
    (child : Fin p.C) (hworld : p.γ child=p.γ root) (hchild : p.lev child ≤ stop)
    (hcut : 0 < cut) (hfr : 0 ≤ fraction)
    {width : ℝ}
    (hwidth : width*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q root j l|) ≤
      frontRadius*((2:ℝ)^p.T (p.lev root)*|(p.Q root).det|))
    (normal : O204.Split.P2) (hnormal : ‖normal‖=1) (offset : ℝ) (rec) :
    (((d.ν k (p.γ root)).prod volume).restrict (data.kept∩p.F child))
      (data.piece rec∩{z | |Inner.inner ℝ normal (Parent.v z.1)-offset| ≤ width}) ≤
      ENNReal.ofReal ((8*fraction)/cut)*
        (((d.ν k (p.γ root)).prod volume).restrict (data.kept∩p.F child)) (data.piece rec) := by
  classical
  let raw := (d.ν k (p.γ root)).prod (volume : Measure ℝ)
  let mu := raw.restrict data.kept
  have hloc := F.record_child_localization hp root child hworld hchild
    (fun rec => rec.1) data.piece (fun rec z hz => (data.subset rec hz).2)
    (fun rec z hz => hEbase (data.subset rec hz).1)
  obtain ⟨hfloorChild,_hratios⟩ := hloc.2 mu
    (fun rec => ENNReal.ofReal cut*raw (F.fineOriginalEvent root rec.1.1 univ)) data.floor
  have hmChild : MeasurableSet (p.F child) :=
    (hp.2.2.2.2.2.2.2 child).2.2.2.2.2.2.2.2.2.1
  have hlaw : mu.restrict (p.F child)=raw.restrict (data.kept∩p.F child) := by
    change (raw.restrict data.kept).restrict (p.F child)=raw.restrict (data.kept∩p.F child)
    rw [Measure.restrict_restrict hmChild,inter_comm]
  have hfloor := hfloorChild rec
  rw [hlaw] at hfloor
  have hf : p.lev rec.1.1=stop :=
    (Finset.mem_filter.mp (F.retained_original_fine_spec root rec.1).1).2.1
  have hw : p.γ rec.1.1=p.γ root :=
    (Finset.mem_filter.mp (F.retained_original_fine_spec root rec.1).1).2.2.1
  by_cases hne : (data.piece rec).Nonempty
  · exact F.current_record_physical_strip_cap hd hp hHE hH root rec.1.1 hactive hf hw hfr
      (data.wide rec hne) (F.retained_original_fine_spec root rec.1).2
      (raw.restrict (data.kept∩p.F child)) Measure.restrict_le_self (data.piece rec)
      (fun z hz => (data.subset rec hz).2) cut hcut hfloor normal hnormal offset hwidth
  · have hempty : data.piece rec=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    apply (measure_mono inter_subset_left).trans
    simp only [hempty,measure_empty,mul_zero,le_refl]

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
