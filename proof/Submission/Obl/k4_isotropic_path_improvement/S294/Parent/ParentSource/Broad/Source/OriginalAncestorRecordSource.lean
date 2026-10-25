-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalAncestorRecordSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UniformAncestorPaletteSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RootPaletteCuts

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open Submission.Lib.K4ListedExceptions
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
open scoped ENNReal

noncomputable section

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}

/-- One actual original ancestor source. Its records, retained law,
reference floors and all later native numerators refer to the same set.
The constructor below supplies every field from genuine preparation. -/
structure OriginalAncestorRecordSource (F : PaletteFamily Q i stop a A θ)
    (root : Fin p.C) (E : Set Ev)
    (K baseRef hiddenRef pv paletteRatio cut frontRadius fraction χ finest dimension Kcap : ℝ) where
  n : ↥(F.retainedOriginalFinePackets root) → ℕ
  code : (deep : ↥(F.retainedOriginalFinePackets root)) → Fin (n deep) → (Fin 4 → ℤ)
  piece : (Σ deep, Fin (n deep)) → Set Ev
  count : ∀ deep, (n deep:ℝ) ≤ K^12
  measurable : ∀ rec, MeasurableSet (piece rec)
  subset : ∀ rec, piece rec⊆E∩F.fineOriginalEvent root rec.1.1 univ
  disjoint : Pairwise (fun r s => Disjoint (piece r) (piece s))
  cover : ∀ z∈E, ∃ rec, z∈piece rec
  wide : ∀ rec, (piece rec).Nonempty → F.coding.code rec.1.1∉
    Q.intrinsicNarrowStates F.code stop F.U frontRadius fraction root
  localization : ∀ rec z, z∈piece rec →
    (fun j => ⌊parentUnshearedCoordinates (d.N k) p root (p.R root) z j /
      ((Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef : Fin 4 → ℝ) j)⌋)∈
      referenceCellOptions
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef)
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef) (code rec.1 rec.2)
  kept : Set Ev
  kept_measurable : MeasurableSet kept
  kept_subset : kept⊆E
  loss : ((d.ν k (p.γ root)).prod volume) (E\kept) ≤
    ENNReal.ofReal cut*(⌈K^12⌉₊:ENNReal)*
      ((d.ν k (p.γ root)).prod volume) {z | (p.γ root,z)∈F.U root}
  floor : ∀ rec, (((d.ν k (p.γ root)).prod volume).restrict kept) (piece rec)=0 ∨
    ENNReal.ofReal cut*((d.ν k (p.γ root)).prod volume)
      (F.fineOriginalEvent root rec.1.1 univ) ≤
        (((d.ν k (p.γ root)).prod volume).restrict kept) (piece rec)
  palette : ∀ rec (D : Set (ℤ×ℤ)), MeasurableSet D →
    (((d.ν k (p.γ root)).prod volume).restrict kept)
      {z | z∈piece rec ∧ velocityPalette pv (v z.1)∈D} ≤
        ENNReal.ofReal ((8*paletteRatio)/cut)*
          (((d.ν k (p.γ root)).prod volume).restrict kept) (piece rec)*
            ((Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette pv)) D
  native_caps : ∀ child : Fin p.C,
      p.γ child=p.γ root →
      δ (d.N k) (p.r (p.lev child)) ≤ δ (d.N k) (p.r (p.lev root)) →
      0 ≤ p.r (p.lev child) → p.lev child ≤ stop →
      p.r (p.lev child)+χ*finest ≤ d.L →
      3*((2:ℝ)^p.T (p.lev child)/(2:ℝ)^p.T (p.lev root))*baseRef ≤ (d.N k^χ)^(-finest) →
      3*(δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*hiddenRef ≤ (d.N k^χ)^(-finest) →
      ∀ r t, finest⁻¹ ≤ r → r ≤ finest → 0 ≤ t → t ≤ finest →
      ∀ q (D : Set (ℤ×ℤ)), MeasurableSet D →
        ((((d.ν k (p.γ root)).prod volume).restrict kept).restrict (p.F child))
          {z | jointCode ((d.N k^χ)^(-r)) ((d.N k^χ)^(-t))
            (fun j => unshearedPacketBase p child z j)
            (physicalParentSignal (d.N k) p child (p.R root) z)=q ∧
          velocityPalette pv (v z.1)∈D} ≤
          ENNReal.ofReal ((8*paletteRatio)/cut)*(625:ENNReal)*
            (ENNReal.ofReal (Kcap*(d.N k^χ)^(-3*r-dimension*t))*
              (d.ν k (p.γ child) (p.A child)*
                ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹)))*
            ((Q.coarseLaw (p.lev root) (F.code root)).map
              (labelledVelocityPalette pv)) D

end Certificate

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

/-- Construct the whole original-law record source in one call. In
particular the retained set is a literal subset of the input source,
and no other ancestor's later cut enters its denominator. -/
theorem ValueBranchData.exists_uniform_ancestor_record_source
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    (root : Fin p.C) (stop : ℕ) (hmid : p.lev root ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r (p.lev root)))
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hbaseSmall : ∀ deep : Fin p.C, p.lev deep = stop →
      p.unshearedDeepRadius root deep ≤ baseMesh)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine = mid → p.lev deep = stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K ^ R)⁻¹ / 12)
    (hheightSmall : ∀ fine deep : Fin p.C, p.lev fine = mid → p.lev deep = stop →
      (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev root)))*
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
    (hEbroad : E⊆broad.residual (p.γ root)∩p.F root)
    (hH₀E : ∀ w, H₀ w⊆d.E k w)
    (hH₀terminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (physicalPaletteMesh paletteRatio : ℝ) (hRatio : 0 ≤ paletteRatio)
    (hOriginal : ∀ b, F.active b → F.U b⊆
      likelihoodGood Q.law (labelledSupport Q.residual)
        (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette physicalPaletteMesh)
        (p.lev root) stop paletteRatio)
    (χ finest : ℝ) (hχ : 0 ≤ χ)
    {dimension f₀ profileError Kcap : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ a, 0 ≤ a → a ≤ d.L → |d.f a-f₀-dimension*a| ≤ profileError)
    (hbudget : 512*(max p.κ (d.K k))^2*p.κ*4^dimension*
      d.N k^(2*profileError+(τ+2*δ₀*d.L)+ε) ≤ Kcap)
    (cut : ℝ) (hcut : 0 < cut) :
    Nonempty (OriginalAncestorRecordSource F root E K baseMesh hidden physicalPaletteMesh
      paletteRatio cut broadRadius broadFraction χ finest dimension Kcap) := by
  let raw := (d.ν k (p.γ root)).prod (volume : Measure ℝ)
  let μ := raw.restrict E
  obtain ⟨n,code,piece,hn,hm,hs,hdj,hcover,hwide,hloc,G,hG,hloss,hfloor,hpalette,_hstrip,hcaps⟩ :=
    V.exists_uniform_ancestor_palette_power_source Q hpure hd hp hHE hHbase hK hmax hpower hκK
      cores root stop hmid hstop hr hrL hD hjets hwidth hbase hhidden hbaseSmall hcoreSmall
      hheightSmall paletteMesh paletteBound paletteFloor F hactive broad E hE hECore hEbroad
      hH₀E hH₀terminal physicalPaletteMesh paletteRatio hRatio hOriginal χ finest hχ hdim hprofile
      hbudget μ le_rfl cut hcut
  let kept := E∩G
  have hkept : MeasurableSet kept := hE.inter hG
  have hlaw : μ.restrict G=raw.restrict kept := by
    change (raw.restrict E).restrict G=raw.restrict (E∩G)
    rw [Measure.restrict_restrict hG,inter_comm G E]
  have hloss' : raw (E\kept) ≤ ENNReal.ofReal cut*(⌈K^12⌉₊:ENNReal)*
      raw {z | (p.γ root,z)∈F.U root} := by
    have hset : Gᶜ∩E=E\kept := by
      ext z
      simp only [kept,mem_inter_iff,mem_compl_iff,mem_sdiff]
      tauto
    simpa only [μ,Measure.restrict_apply' hE,hset] using hloss
  refine ⟨{
    n := n
    code := code
    piece := piece
    count := hn
    measurable := hm
    subset := hs
    disjoint := hdj
    cover := hcover
    wide := hwide
    localization := hloc
    kept := kept
    kept_measurable := hkept
    kept_subset := inter_subset_left
    loss := hloss'
    floor := ?_
    palette := ?_
    native_caps := ?_ }⟩
  · simpa only [hlaw] using hfloor
  · simpa only [hlaw] using hpalette
  · simpa only [hlaw] using hcaps

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
