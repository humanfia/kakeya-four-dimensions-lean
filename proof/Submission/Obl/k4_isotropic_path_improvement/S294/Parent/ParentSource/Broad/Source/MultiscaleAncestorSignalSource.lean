-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.MultiscaleAncestorSignalSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/MultiscaleAncestorSignalSource.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorSignalPowerSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.MultiscaleCoreSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalDescendantReferences

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open scoped ENNReal BigOperators

noncomputable section

/-- Construct one common original ancestor-R source for all registered
fine depths BEFORE any later child or query mesh is selected. Each depth
costs the same full original ROOT reference; no child count or child
renormalization occurs. Every surviving subset inherits the actual
relative-coordinate power menus at all registered fine depths. -/
theorem BroadMultiscaleCoreSource.exists_ancestor_signal_layer_source
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {m n : ℕ} {K : ℝ} {e R : ℕ} {depth : Fin n → ℕ}
    {H₀ original : Fin (d.W k) → Set Event} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H₀ u τ) (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (C : BroadMultiscaleCoreSource d k p original n depth K e R)
    (hHE : ∀ w, original w⊆d.E k w) (hHbase : ∀ w, original w⊆Q.base w)
    (hHterminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hHbroad : ∀ w, original w⊆broad.residual w)
    (root : Fin p.C) (hroot : p.lev root=i) (hactive : F.active root)
    (hmid : ∀ j, p.lev root ≤ depth j) (hstop : ∀ j, depth j ≤ stop)
    (hr : ∀ j, 0 ≤ p.r (depth j)) (hrL : ∀ j, p.r (depth j) ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : ∀ j, δ (d.N k) (p.r (depth j)) ≤ δ (d.N k) (p.r (p.lev root)))
    {Kc width θrow : ℝ} {qc : ℕ} (hKc : 2*K^((3*R+58)+7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc^qc)⁻¹ ≤ width)
    (hstrip : width*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (hdeep : ∀ j, ∀ fine deep : Fin p.C, p.lev fine=depth j → p.lev deep=stop →
      6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ renewalCellMesh Kc J qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ fraction)
    (δref : ENNReal) (hδ0 : δref≠0) (hδtop : δref≠∞)
    (hβ1 : δref⁻¹*ENNReal.ofReal (8*fraction)<1)
    (source : Set Event) (hsource : MeasurableSet source)
    (hsub : source⊆C.current (p.γ root)∩p.F root)
    {Kgeom : ℝ} (hKK : K ≤ Kgeom)
    (hgeometry : d.N k^(2*δ₀*d.L) ≤ Kgeom) (hconstant : 96*coreRowK₀ ≤ Kgeom)
    (w t : ℕ) (hwidthPower : (Kgeom^w)⁻¹ ≤ width) (hθPower : (Kgeom^t)⁻¹ ≤ θrow)
    (hκ₁ : κ₁ ≤ 1) (hmidm : ∀ j, depth j < m) :
    let gp := ((3*R+58)+8)*J+w+t*⌈coreRowC₀⌉₊+1;
    let reference := d.ν k (p.γ root) (p.A root)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹);
    let cost := ENNReal.ofReal (4*K^(3*R+28)*p.κ^2)*
      (ENNReal.ofReal (θrow*(K^R)⁻¹)+27*(δref*ENNReal.ofReal (p.κ^2)));
    ∃ current : Set Event, MeasurableSet current ∧ current⊆source ∧
      ((d.ν k (p.γ root)).prod volume) source ≤
        ((d.ν k (p.γ root)).prod volume) current+(n:ENNReal)*cost*reference ∧
      ∀ j : Fin n, ∀ child : Fin p.C,
        p.γ child=p.γ root → p.lev child ≤ depth j → s (p.lev child) ≤ s (depth j) →
      ∀ S : Set Event, S⊆current∩p.F child →
      ∀ dimension profileError : ℝ, 0 ≤ dimension → dimension ≤ 1 →
        d.f (p.r (depth j))-d.f (p.r (p.lev child)) ≤
          dimension*(p.r (depth j)-p.r (p.lev child))+profileError →
        d.N k^profileError ≤ Kgeom →
      ∀ basePower heightPower : ℕ, ∀ base hidden : ℝ, 0 < base → 0 < hidden →
        Kgeom^(gp+10)*(δ (d.N k) (p.r (depth j))/δ (d.N k) (p.r (p.lev child))) ≤ hidden →
        Kgeom^(gp+12)*((2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev child))*base ≤
          (δ (d.N k) (p.r (p.lev child))/δ (d.N k) (p.r (p.lev root)))*hidden →
        base ≤ Kgeom^basePower*(δ (d.N k) (p.r (depth j))/δ (d.N k) (p.r (p.lev child))) →
        hidden ≤ Kgeom^heightPower*(δ (d.N k) (p.r (depth j))/δ (d.N k) (p.r (p.lev child))) →
        ∃ menu : Finset (Fin 4 → ℤ),
          (menu.card : ℝ)*base^3*hidden^dimension ≤ Kgeom^(3*basePower+3*R+heightPower+73) ∧
          (menu.card : ℝ) ≤ Kgeom^(3*basePower+3*R+heightPower+73)/(base^3*hidden^dimension) ∧
          ∀ z∈S, jointCode base hidden (fun j => unshearedPacketBase p child z j)
            (physicalParentSignal (d.N k) p child (p.R root) z)∈menu := by
  classical
  let raw : Measure Event := (d.ν k (p.γ root)).prod volume
  let reference := d.ν k (p.γ root) (p.A root)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹)
  let cost := ENNReal.ofReal (4*K^(3*R+28)*p.κ^2)*
    (ENNReal.ofReal (θrow*(K^R)⁻¹)+27*(δref*ENNReal.ofReal (p.κ^2)))
  have hf (j : Fin n) := (C.values j).exists_power_ancestor_signal_joint_source Q hpure hd hp
    (fun w => (C.subset j w).trans (hHE w)) (fun w => (C.subset j w).trans (hHbase w))
    hHterminal hK hmax hpower hκK (C.cores j) broad
    (fun w => (C.subset j w).trans (hHbroad w)) root hroot hactive
    (hmid j) (hstop j) (hr j) (hrL j) hD hjets (hwidth j) hKc hwidthpos hwidthfloor
    hstrip (hdeep j) hθrow hθrow1 hfraction δref hδ0 hδtop hβ1 source hsource
    (fun z hz => ⟨C.current_cores j _ (hsub hz).1,(hsub hz).2⟩)
    hKK hgeometry hconstant w t hwidthPower hθPower hκ₁ (hmidm j)
  choose cut hcut hcutSub hloss hcount using hf
  let current := source∩⋂ j, cut j
  have hcurrent : MeasurableSet current := hsource.inter (MeasurableSet.iInter hcut)
  have hcurrentCut (j : Fin n) : current⊆cut j := fun z hz => mem_iInter.mp hz.2 j
  letI : IsProbabilityMeasure (d.ν k (p.γ root)) := (hd.weights k).2.2 _
  have hreferenceTop : reference≠∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hsourceF : source⊆p.F root := fun z hz => (hsub hz).2
  have hFmass : raw (p.F root) ≤ reference := by
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 root
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -⟩ := hch
    exact Broad.prod_le_prior_mul_block
      (fun z (hz : z∈p.F root) => ⟨(hF z hz).2.1,(hF z hz).2.2.1⟩)
  have hsourceTop : raw source≠∞ :=
    ne_of_lt (((measure_mono hsourceF).trans hFmass).trans_lt (lt_top_iff_ne_top.mpr hreferenceTop))
  have hdiscard (j : Fin n) : raw (source\cut j) ≤ cost*reference :=
    (measure_sdiff_le_iff_le_add (hcut j).nullMeasurableSet (hcutSub j)
      (ne_of_lt ((measure_mono (hcutSub j)).trans_lt (lt_top_iff_ne_top.mpr hsourceTop)))).mpr (hloss j)
  have hdiscardAll : raw (source\current) ≤ (n:ENNReal)*cost*reference := by
    have hcover : source\current⊆⋃ j, source\cut j := by
      intro z hz
      by_contra h
      apply hz.2
      refine ⟨hz.1,mem_iInter.mpr ?_⟩
      intro j
      by_contra hj
      exact h (mem_iUnion.mpr ⟨j,hz.1,hj⟩)
    calc
      _ ≤ raw (⋃ j, source\cut j) := measure_mono hcover
      _ ≤ ∑ j, raw (source\cut j) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ j : Fin n, cost*reference := Finset.sum_le_sum (fun j _ => hdiscard j)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc]
  refine ⟨current,hcurrent,inter_subset_left,?_,?_⟩
  · apply (measure_mono (show source⊆current∪(source\current) from fun z hz => by
      by_cases h : z∈current
      · exact Or.inl h
      · exact Or.inr ⟨hz,h⟩)).trans
    exact (measure_union_le _ _).trans (add_le_add le_rfl hdiscardAll)
  intro j child hworld hchild hsChild S hS
  exact hcount j child hworld hchild hsChild S
    (fun z hz => ⟨hcurrentCut j (hS hz).1,(hS hz).2⟩)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
