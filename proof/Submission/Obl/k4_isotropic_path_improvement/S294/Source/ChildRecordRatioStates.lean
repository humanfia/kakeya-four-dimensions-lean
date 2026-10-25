-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.ChildRecordRatioStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Extends this LOT tree o294, x1082 commit33f61bf32,
-- Source/StagesAssembly.lean, child_states_of_records, using the actual
-- source and ratio constructors proved on x1095. No external formal code.
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.AncestorRecordChildRatios
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SimultaneousChildStates

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily
  velocityPalette labelledVelocityPalette)
open scoped ENNReal BigOperators

noncomputable section

/-- Both strip coordinate systems and the fixed all-D original fine
palette on one actual current graph-code law. -/
def GraphRecordRatios {W : ℕ} (p : PathData W) (N : ℝ) (root : Fin p.C)
    (graphMesh finePv radius stripWidth : ℝ) (stripCoeff paletteCoeff : ENNReal)
    (raw : Measure Ev) (E : Set Ev) (palette : Measure (ℤ×ℤ)) : Prop :=
  let code := clockParentCode p root (Parent.SignalGraph.ancestorSignal N p root) graphMesh
  (∀ label (normal center : EuclideanSpace ℝ (Fin 2)), ‖normal‖=1 →
    (raw.restrict E) {z | code z=label ∧
      |Inner.inner ℝ normal ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center)| ≤ radius} ≤
      stripCoeff*(raw.restrict E) {z | code z=label}) ∧
  (∀ label (normal : O204.Split.P2) offset, ‖normal‖=1 →
    (raw.restrict E) {z | code z=label ∧ |Inner.inner ℝ normal (Parent.v z.1)-offset| ≤ stripWidth} ≤
      stripCoeff*(raw.restrict E) {z | code z=label}) ∧
  ∀ label (D : Set (ℤ×ℤ)), MeasurableSet D →
    (raw.restrict E) {z | code z=label ∧ velocityPalette finePv (Parent.v z.1)∈D} ≤
      paletteCoeff*(raw.restrict E) {z | code z=label}*palette D

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

/-- Actual records construct the final states of ALL children together,
with SAME-slice normalized-pencil and original-velocity strip bounds and
all-D original palette domination on every ancestor graph code. The sole
loss is 6561*beta against the global original reference budget. -/
theorem child_states_with_ratios {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal}
    {F : PaletteFamily Q i stop meshF envF θF} (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (selected : Set (Fin p.C)) (level : ℕ) (hlevel : ∀ b ∈ selected, p.lev b = level)
    (anc : Fin p.C → Fin p.C)
    (hanc : ∀ b ∈ selected, F.active (anc b) ∧ p.γ b = p.γ (anc b) ∧ p.lev b ≤ stop)
    {Edata : Fin p.C → Set Ev}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension
      Kcap : ℝ}
    (data : (a : Fin p.C) → F.active a → OriginalAncestorRecordSource F a (Edata a) Krecord
      baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension Kcap)
    (hEdata : ∀ a, F.active a → Edata a ⊆ Q.base (p.γ a))
    (E : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w)) (hEbase : ∀ w, E w ⊆ Q.base w)
    (hkept : ∀ b (hb : b ∈ selected), E (p.γ b) ∩ p.F b ⊆ (data (anc b) (hanc b hb).1).kept)
    {K ε pv aA q graphMesh : ℝ} (hK : 0 < K) (heps : 0 < ε) (haA : 0 < aA) (hq : 0 < q)
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hcut : 0 < cut) (hfr : 0 ≤ fraction)
    (hgraph : 0 < graphMesh) (hfinePv : 0 < finePv) (hpv : finePv ≤ pv)
    (hgraphBase : 3 * baseRef ≤ graphMesh) (hgraphHidden : 3 * hiddenRef ≤ graphMesh)
    (hphysicalBase : ∀ b ∈ selected,
      3 * ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev (anc b))) * baseRef ≤ ε)
    (hphysicalHidden : ∀ b ∈ selected,
      3 * (δ (d.N k) (p.r (p.lev (anc b))) / δ (d.N k) (p.r (p.lev b))) * hiddenRef ≤
        (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev b))) * ε)
    (beta : ENNReal) (hbeta : beta ≠ 0) (hbetaTop : beta ≠ ⊤)
    (hstripWidth : ∀ b ∈ selected,
      (K / 4) ^ (-100 : ℝ) * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (anc b) j l|) ≤
        frontRadius * ((2 : ℝ) ^ p.T (p.lev (anc b)) * |(p.Q (anc b)).det|))
    (hstripRatio : ENNReal.ofReal ((8 * fraction) / cut) / beta ≤ (1 / 2000000000000 : ENNReal))
    (hpaletteRatio : ENNReal.ofReal ((8 * paletteRatio) / cut) / beta ≤ ENNReal.ofReal (K / 4))
    (row : Fin p.C → (Fin 4 → ℤ) → Fin 3 → ℝ) {Brow : ℝ} (hBrow : 0 ≤ Brow)
    (hrow : ∀ a c j, |row a c j| ≤ Brow)
    (radius stripWidth : ℝ) (hNormalizedWidth : (6*p.κ)*radius ≤ frontRadius)
    (hOriginalWidth : ∀ b∈selected,
      stripWidth*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q (anc b) j l|) ≤
        frontRadius*((2:ℝ)^p.T (p.lev (anc b))*|(p.Q (anc b)).det|)) :
    ∃ (keep : Fin (d.W k) → Set Ev)
      (localKeep : (b : Fin p.C) → b ∈ selected → Set Ev)
      (state : (b : Fin p.C) → b ∈ selected → Ev → ℕ)
      (value : (b : Fin p.C) → b ∈ selected → ℕ → Fin 3 → ℝ)
      (palette : (b : Fin p.C) → b ∈ selected → Measure (Fin 2 → ℤ)),
      (∀ w, MeasurableSet (keep w) ∧ keep w ⊆ E w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w \ keep w)) ≤
        (6561 : ENNReal) * beta ∧
      ∀ b (hb : b ∈ selected),
        keep (p.γ b) ∩ p.F b = localKeep b hb ∧
        StateClauses K ε pv (d.ν k (p.γ b)) (unshearedPacketBase p b)
          (fun z => MvPolynomial.eval (xp z.1 z.2) (p.R (anc b)) / δ (d.N k) (p.r (p.lev b)))
          (keep (p.γ b) ∩ p.F b) (state b hb) (palette b hb) ∧
        (∀ z, value b hb (state b hb z) = (aA / q) • row (anc b) (clockParentCode p (anc b)
          (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b)) graphMesh z)) ∧
        (∀ j c, |value b hb j c| ≤ (aA / q) * Brow) ∧
        (∀ x y, state b hb x = state b hb y →
          clockParentCode p (anc b) (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b))
            graphMesh x =
          clockParentCode p (anc b) (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b))
            graphMesh y) ∧
        GraphRecordRatios p (d.N k) (anc b) graphMesh finePv radius stripWidth
          (ENNReal.ofReal ((8*fraction)/cut)/beta)
          (ENNReal.ofReal ((8*paletteRatio)/cut)/beta)
          ((d.ν k (p.γ b)).prod volume) (keep (p.γ b)∩p.F b)
          ((Q.coarseLaw (p.lev (anc b)) (F.code (anc b))).map (labelledVelocityPalette finePv)) := by
  classical
  have hscale0 : 0 ≤ aA/q := (div_pos haA hq).le
  have hF (b) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  apply assemble_simultaneous_child_states_with_extra Q hd hp selected level hlevel E hE hEbase K
    (fun _ => ε) (fun _ => pv) (fun b => unshearedPacketBase p b)
    (fun b z => MvPolynomial.eval (xp z.1 z.2) (p.R (anc b))/δ (d.N k) (p.r (p.lev b)))
    (fun b => clockParentCode p (anc b) (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b)) graphMesh)
    (fun b c => (aA/q) • row (anc b) c) (fun _ => (aA/q)*Brow) ((6561:ENNReal)*beta)
    (fun b keepb _ _ _ => GraphRecordRatios p (d.N k) (anc b) graphMesh finePv radius stripWidth
      (ENNReal.ofReal ((8*fraction)/cut)/beta) (ENNReal.ofReal ((8*paletteRatio)/cut)/beta)
      ((d.ν k (p.γ b)).prod volume) keepb
      ((Q.coarseLaw (p.lev (anc b)) (F.code (anc b))).map (labelledVelocityPalette finePv)))
  intro b hb
  obtain ⟨hact,hworld,hstop⟩ := hanc b hb
  have hδb : 0 < δ (d.N k) (p.r (p.lev b)) := by unfold δ; positivity
  have hrow' : ∀ c j, |((aA/q) • row (anc b) c) j| ≤ (aA/q)*Brow := by
    intro c j
    simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hscale0]
    exact mul_le_mul_of_nonneg_left (hrow _ c j) hscale0
  obtain ⟨keepb,state,value,palette,hsub,hloss,hstates,hvalue,hbound,hfaith,_hstateRatios,hgraphRatios⟩ :=
    OriginalAncestorRecordSource.relative_states_with_record_ratios (data (anc b) hact) hd hp hHE hH
      hact (hEdata _ hact) b hworld hstop hbaseRef hhiddenRef hcut hfr hgraph heps hδb hfinePv
      hpv hK hgraphBase hgraphHidden (hphysicalBase b hb) (hphysicalHidden b hb)
      (E (p.γ b)∩p.F b) ((hE _).inter (hF b)) (fun z hz => ⟨hkept b hb hz,hz.2⟩)
      beta hbeta hbetaTop (fun c => (aA/q) • row (anc b) c) (mul_nonneg hscale0 hBrow)
      hrow' (hstripWidth b hb) hstripRatio hpaletteRatio
  refine ⟨keepb,state,value,palette,hsub,?_,?_,hvalue,hbound,hfaith,?_⟩
  · rw [←hworld] at hloss
    simpa only [mul_assoc] using hloss
  · rw [hworld]
    exact hstates
  · rw [hworld]
    refine ⟨?_,?_,?_⟩
    · intro label normal center hnormal
      exact hgraphRatios _ (ENNReal.ofReal ((8*fraction)/cut))
        (fun rec => OriginalAncestorRecordSource.child_record_normalized_strip_cap (data (anc b) hact) hd hp hHE hH hact
          (hEdata _ hact) b hworld hstop hcut hfr radius hNormalizedWidth normal center hnormal rec) label
    · intro label normal offset hnormal
      exact hgraphRatios _ (ENNReal.ofReal ((8*fraction)/cut))
        (fun rec => OriginalAncestorRecordSource.child_record_original_strip_cap (data (anc b) hact) hd hp hHE hH hact
          (hEdata _ hact) b hworld hstop hcut hfr (hOriginalWidth b hb) normal hnormal offset rec) label
    · intro label D hD
      have h := hgraphRatios _
        (ENNReal.ofReal ((8*paletteRatio)/cut)*
          ((Q.coarseLaw (p.lev (anc b)) (F.code (anc b))).map (labelledVelocityPalette finePv)) D)
        (fun rec => OriginalAncestorRecordSource.child_record_palette_cap (data (anc b) hact) hd hp (hEdata _ hact)
          b hworld hstop D hD rec) label
      calc
        _ ≤ _ := h
        _ = _ := by
          let piD : ENNReal :=
            ((Q.coarseLaw (p.lev (anc b)) (F.code (anc b))).map (labelledVelocityPalette finePv)) D
          let massCell : ENNReal := (((d.ν k (p.γ (anc b))).prod volume).restrict keepb)
            {z | clockParentCode p (anc b) (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b))
              graphMesh z=label}
          change ((ENNReal.ofReal ((8*paletteRatio)/cut)*piD)/beta)*massCell=
            (ENNReal.ofReal ((8*paletteRatio)/cut)/beta)*massCell*piD
          simp only [div_eq_mul_inv]
          ac_rfl

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
