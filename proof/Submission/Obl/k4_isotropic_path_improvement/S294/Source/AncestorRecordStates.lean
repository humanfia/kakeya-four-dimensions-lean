-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.AncestorRecordStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
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

/-- The actual global ancestor record source gives final physical
states after ANY later child/source choice. Child localization preserves
its original floors; one two-query keep transfers breadth and palette;
the final nonaligned velocity width pays four without another cut.
The deletion is charged to the FULL child reference. -/
theorem OriginalAncestorRecordSource.relative_states_with_pencil_breadth
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
    (hpaletteRatio : ENNReal.ofReal ((8*paletteRatio)/cut)/beta ≤ ENNReal.ofReal (K/4))
    (radius : ℝ) (hwidth : (6*p.κ)*radius ≤ frontRadius) :
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
      (∀ j (normal center : EuclideanSpace ℝ (Fin 2)), ‖normal‖=1 →
        (((d.ν k (p.γ root)).prod volume).restrict keep)
          {z | state z=j ∧
            |Inner.inner ℝ normal ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center)| ≤ radius} ≤
          (ENNReal.ofReal ((8*fraction)/cut)/beta)*
            (((d.ν k (p.γ root)).prod volume).restrict keep) {z | state z=j}) ∧
      ∀ label (normal center : EuclideanSpace ℝ (Fin 2)), ‖normal‖=1 →
        (((d.ν k (p.γ root)).prod volume).restrict keep)
          {z | clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root)
            graphMesh z=label ∧
            |Inner.inner ℝ normal ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center)| ≤ radius} ≤
          (ENNReal.ofReal ((8*fraction)/cut)/beta)*
            (((d.ν k (p.γ root)).prod volume).restrict keep)
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
  have hPencilCap (normal center : EuclideanSpace ℝ (Fin 2)) (hnormal : ‖normal‖=1) (rec) :
      (raw.restrict reservoir) (data.piece rec∩
        {z | |Inner.inner ℝ normal ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center)| ≤ radius}) ≤
          ENNReal.ofReal ((8*fraction)/cut)*(raw.restrict reservoir) (data.piece rec) := by
    have hf : p.lev rec.1.1=stop :=
      (Finset.mem_filter.mp (F.retained_original_fine_spec root rec.1).1).2.1
    have hw : p.γ rec.1.1=p.γ root :=
      (Finset.mem_filter.mp (F.retained_original_fine_spec root rec.1).1).2.2.1
    by_cases hne : (data.piece rec).Nonempty
    · exact F.current_record_scaled_normalized_strip_cap hd hp hHE hH root rec.1.1 hactive hf hw
        hfr (data.wide rec hne) (F.retained_original_fine_spec root rec.1).2
        (raw.restrict reservoir) Measure.restrict_le_self (data.piece rec)
        (fun z hz => (data.subset rec hz).2) cut hcut (hfloor rec) radius hwidth normal center hnormal
    · have hempty : data.piece rec=∅ := Set.not_nonempty_iff_eq_empty.mp hne
      apply (measure_mono inter_subset_left).trans
      simp only [hempty,measure_empty,mul_zero,le_refl]
  refine ⟨keep,state,value,palette,hkeepSub,?_,hcoarse,hvalue,hvalueBound,hgraphFaith,?_,?_⟩
  · exact hloss.trans (add_le_add_right (mul_le_mul' le_rfl hreference) _)
  · intro j normal center hnormal
    exact hstateRatios _ (ENNReal.ofReal ((8*fraction)/cut)) (hPencilCap normal center hnormal) j
  · intro label normal center hnormal
    exact hgraphRatios _ (ENNReal.ofReal ((8*fraction)/cut)) (hPencilCap normal center hnormal) label

/-- The graph-faithful interface retains its previous output shape. -/
theorem OriginalAncestorRecordSource.relative_states_with_graph_code
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
      ∀ x y, state x=state y →
        clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh x=
        clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh y := by
  have hc : 0 < 6*p.κ := by linarith [hp.1]
  have hwidth : (6*p.κ)*(frontRadius/(6*p.κ)) ≤ frontRadius := by
    apply le_of_eq
    have hκ : p.κ≠0 := ne_of_gt (by linarith [hp.1])
    field_simp [hκ]
  obtain ⟨keep,state,value,palette,hkeep,hloss,hstates,hvalue,hbound',hfaith,_hstatePencil,_hgraphPencil⟩ :=
    OriginalAncestorRecordSource.relative_states_with_pencil_breadth data hd hp hHE hH hactive hEbase
      child hworld hchild hbaseRef hhiddenRef hcut hfr hgraph heps haEff hfinePv hpv hK
      hgraphBase hgraphHidden hphysicalBase hphysicalHidden S hS hSsub beta hbeta hbetaTop
      row hbound hrow hstripWidth hstripRatio hpaletteRatio (frontRadius/(6*p.κ)) hwidth
  exact ⟨keep,state,value,palette,hkeep,hloss,hstates,hvalue,hbound',hfaith⟩

/-- The original child-state interface, retaining its previous output shape. -/
theorem OriginalAncestorRecordSource.relative_states
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
      ∀ j c, |value j c| ≤ bound := by
  obtain ⟨keep,state,value,palette,hkeep,hloss,hstates,hvalue,hbound',_hfaith⟩ :=
    OriginalAncestorRecordSource.relative_states_with_graph_code data hd hp hHE hH hactive hEbase
      child hworld hchild hbaseRef hhiddenRef hcut hfr hgraph heps haEff hfinePv hpv hK
      hgraphBase hgraphHidden hphysicalBase hphysicalHidden S hS hSsub beta hbeta hbetaTop
      row hbound hrow hstripWidth hstripRatio hpaletteRatio
  exact ⟨keep,state,value,palette,hkeep,hloss,hstates,hvalue,hbound'⟩


/-- The same actual source supplies the graph stage's exact breadth
renewal after every later measurable source restriction. -/
theorem OriginalAncestorRecordSource.graph_breadth_renewal
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hactive : F.active root)
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hcut : 0 < cut) (hfr : 0 ≤ fraction)
    {mesh radius ratio : ℝ} (hmesh : 0 < mesh)
    (hbaseBudget : 3*baseRef ≤ mesh) (hhiddenBudget : 3*hiddenRef ≤ mesh)
    (beta : ENNReal) (hbeta : beta≠0) (hbetaTop : beta≠⊤)
    (hwidth : (6*p.κ)*radius ≤ frontRadius)
    (hratio : ENNReal.ofReal ((8*fraction)/cut)/beta ≤ ENNReal.ofReal ratio) :
    ∀ middle : Set Ev, MeasurableSet middle → middle⊆data.kept →
    ∃ current : Set Ev, MeasurableSet current ∧ current⊆middle ∧
      ((d.ν k (p.γ root)).prod volume) middle ≤ ((d.ν k (p.γ root)).prod volume) current+
        (81:ENNReal)*beta*((d.ν k (p.γ root)).prod volume) data.kept ∧
      ∀ label (normal center : EuclideanSpace ℝ (Fin 2)), ‖normal‖=1 →
        (((d.ν k (p.γ root)).prod volume).restrict current)
          {z | clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) mesh z=label ∧
            |Inner.inner ℝ normal ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center)| ≤ radius} ≤
          ENNReal.ofReal ratio*(((d.ν k (p.γ root)).prod volume).restrict current)
            ((clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) mesh) ⁻¹' {label}) := by
  intro middle hmiddle hmiddleSub
  obtain ⟨current,hcurrent,hsub,hloss,hcaps⟩ :=
    F.ancestor_clock_breadth_renewal hd hp hHE hH root hactive data.n data.code data.piece
      data.measurable data.disjoint (fun rec z hz => (data.subset rec hz).2) hfr data.wide
      data.kept data.kept_measurable (fun z hz => data.cover z (data.kept_subset hz))
      cut hcut data.floor hbaseRef hhiddenRef hmesh data.localization
      hbaseBudget hhiddenBudget beta hbeta hbetaTop radius hwidth middle hmiddle hmiddleSub
  refine ⟨current,hcurrent,hsub,hloss,?_⟩
  intro label normal center hnormal
  exact (hcaps label normal center hnormal).trans (mul_le_mul' hratio le_rfl)

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
