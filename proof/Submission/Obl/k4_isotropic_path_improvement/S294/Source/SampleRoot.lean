-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleRoot, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootCensusPackage
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.FixedSourcePowers

/-!
# The root stage of one sample (session x1082)

`sample_core_records`: the multiscale core source of the sample (`FixedSourcePowers.coreFactory`,
consecutive depths `i, i+1, …, i + nfam - 1`) and x1095's record sources of all active ancestors
on its retained events (`ValueBranchData.exists_all_ancestor_record_sources` at the record depth
`jrec`), with the two mass losses.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual
  likelihoodGood labelledSupport finitePacketHistory labelledVelocityPalette)
open scoped ENNReal

noncomputable section

/-- The native envelope of a sample's core source. -/
abbrev coreK {d : ProblemData} {k : ℕ} (p : PathData (d.W k)) (τ : ℝ) : ℝ :=
  Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ)

section Sample

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

/-- **The core source and the record sources of a sample.** -/
theorem sample_core_records (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {H : Fin (d.W k) → Set Ev} (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {τ : ℝ} (hτ : 0 ≤ τ) (Qp : PreparedAngularPath d k p m H (fun _ : Fin 1 => d.η * d.L) τ)
    (hpure : Qp.uniformPureBounds τ)
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} (Fp : PaletteFamily Qp i stop meshF envF θF)
    {rF frF : ℝ} (Rp : BroadResidual Fp rF frF)
    -- the core depth family
    (nfam : ℕ) (hdepth : ∀ j : Fin nfam, i + (j : ℕ) < m)
    (hr : ∀ j : Fin nfam, 0 ≤ p.r (i + (j : ℕ))) (hrL : ∀ j : Fin nfam, p.r (i + (j : ℕ)) ≤ d.L)
    (hn : (nfam : ℝ) ≤ Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ))
    -- the record depth and the record numerics
    (jrec : Fin nfam) (hjstop : i + (jrec : ℕ) ≤ stop)
    (hwidthrec : δ (d.N k) (p.r (i + (jrec : ℕ))) ≤ δ (d.N k) (p.r i))
    {baseRef hiddenRef : ℝ} (hbase : 0 < baseRef) (hhidden : 0 < hiddenRef)
    (hbaseSmall : ∀ root : Fin p.C, p.lev root = i → ∀ deep : Fin p.C, p.lev deep = stop →
      p.unshearedDeepRadius root deep ≤ baseRef)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine = i + (jrec : ℕ) → p.lev deep = stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤
        (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^
          FixedSourcePowers.coreRadius)⁻¹ / 12)
    (hheightSmall : ∀ root : Fin p.C, p.lev root = i →
      ∀ fine deep : Fin p.C, p.lev fine = i + (jrec : ℕ) → p.lev deep = stop →
      (δ (d.N k) (p.r (p.lev root)) / δ (d.N k) (p.r (p.lev root))) *
        (2 * (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^ 14 *
          (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^ 6)⁻¹ *
          (δ (d.N k) (p.r (i + (jrec : ℕ))) / δ (d.N k) (p.r (p.lev root)))) +
          ((Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^
              ((3 * FixedSourcePowers.coreRadius + 58) + 7)) ^ FixedSourcePowers.jet *
            (p.κ + Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^ 14 *
              (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^ 6)⁻¹)) *
            (6 * Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^
              FixedSourcePowers.coreRadius * p.deepBaseRadius (d.N k) d.L δ₀ fine deep)) ≤
        hiddenRef)
    (pv paletteRatio : ℝ) (hRatio : 0 ≤ paletteRatio)
    (hOriginal : ∀ b, Fp.active b → Fp.U b ⊆ likelihoodGood Qp.law (labelledSupport Qp.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette pv) i stop paletteRatio)
    (χ finest : ℝ) (hχ : 0 ≤ χ)
    {dimension f₀ profileError Kcap : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ x, 0 ≤ x → x ≤ d.L → |d.f x - f₀ - dimension * x| ≤ profileError)
    (hbudget : 512 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
      d.N k ^ (2 * profileError + (τ + 2 * δ₀ * d.L) + τ) ≤ Kcap)
    (cut : ℝ) (hcut : 0 < cut) :
    ∃ (C : BroadMultiscaleCoreSource d k p Rp.residual nfam (fun j => i + (j : ℕ))
        (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ))
        FixedSourcePowers.coreE FixedSourcePowers.coreRadius)
      (data : (a : Fin p.C) → Fp.active a → OriginalAncestorRecordSource Fp a
        (C.current (p.γ a) ∩ p.F a) (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ))
        baseRef hiddenRef pv paletteRatio cut rF frF χ finest dimension Kcap)
      (K2 : Fin (d.W k) → Set Ev),
      (∀ w, MeasurableSet (K2 w) ∧ K2 w ⊆ C.current w) ∧
      (∀ a (ha : Fp.active a), K2 (p.γ a) ∩ p.F a = (data a ha).kept) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w)) ≤
        (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (K2 w)) +
          ENNReal.ofReal cut *
            (⌈Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^ 12⌉₊ : ENNReal) +
          ENNReal.ofReal (p.κ⁻¹ / 64) := by
  have hN1 : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hκ1 : 1 ≤ p.κ := hp.1
  have htol : 0 ≤ τ + τ := by linarith
  obtain ⟨hK2304, hκK, hmax, hpower⟩ :=
    Submission.Lib.K4NativePreparationNumerics.native_pre_geometry_envelope_bounds
      (source := d.K k) hκ1 hN1 htol
  obtain ⟨C, hCloss⟩ := FixedSourcePowers.coreFactory hd hp Qp hpure htol hH Rp nfam
    (fun j => i + (j : ℕ)) hdepth hr hrL hn
  have hresE : ∀ w, Rp.residual w ⊆ d.E k w := fun w z hz => hHE w (Rp.subset_H w hz)
  have hresB : ∀ w, Rp.residual w ⊆ Qp.base w := fun w => broadResidual_subset_base Rp w
  have hsrcE : ∀ w, C.source jrec w ⊆ d.E k w := fun w => (C.subset jrec w).trans (hresE w)
  have hsrcB : ∀ w, C.source jrec w ⊆ Qp.base w := fun w => (C.subset jrec w).trans (hresB w)
  obtain ⟨sources, K2, hK2, hK2loss, hK2slice⟩ :=
    (C.values jrec).exists_all_ancestor_record_sources Qp hpure hd hp hsrcE hsrcB
      hK2304 hmax hpower hκK (C.cores jrec) i stop (by omega) hjstop (hr jrec) (hrL jrec)
      (le_refl 5186) FixedSourcePowers.jet_bound hwidthrec hbase hhidden hbaseSmall hcoreSmall
      hheightSmall meshF envF θF Fp Rp C.current C.current_measurable
      (fun w => C.current_cores jrec w) C.current_subset hHE hH pv paletteRatio hRatio hOriginal
      χ finest hχ hdim hprofile hbudget cut hcut
  refine ⟨C, sources, K2, fun w => ⟨(hK2 w).1, (hK2 w).2⟩, hK2slice, ?_⟩
  -- the mass chain
  have hsplit (A B : Fin (d.W k) → Set Ev) :
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (A w)) ≤
        (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (B w)) +
          ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (A w \ B w) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [← mul_add]
    refine mul_le_mul' le_rfl ((measure_mono (fun z hz => ?_)).trans
      (measure_union_le (B w) (A w \ B w)))
    by_cases hB : z ∈ B w
    · exact Or.inl hB
    · exact Or.inr ⟨hz, hB⟩
  calc (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w))
      ≤ (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (C.current w)) +
          ENNReal.ofReal (p.κ⁻¹ / 64) := (hsplit _ _).trans (add_le_add le_rfl hCloss)
    _ ≤ ((∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (K2 w)) +
          ENNReal.ofReal cut *
            (⌈Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^ 12⌉₊ : ENNReal)) +
          ENNReal.ofReal (p.κ⁻¹ / 64) :=
        add_le_add ((hsplit _ _).trans (add_le_add le_rfl hK2loss)) le_rfl

open Submission.Lib.K4ParentSignalPreparation.Census in
/-- **The root package of a sample.** -/
theorem sample_root_package (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {H : Fin (d.W k) → Set Ev} (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {τ : ℝ} (hτ : 0 ≤ τ) (Qp : PreparedAngularPath d k p m H (fun _ : Fin 1 => d.η * d.L) τ)
    (hpure : Qp.uniformPureBounds τ)
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} (Fp : PaletteFamily Qp i stop meshF envF θF)
    {rF frF : ℝ} (Rp : BroadResidual Fp rF frF) {nfam : ℕ}
    (C : BroadMultiscaleCoreSource d k p Rp.residual nfam (fun j => i + (j : ℕ)) (coreK p τ)
        FixedSourcePowers.coreE FixedSourcePowers.coreRadius)
    {baseRef hiddenRef pv paletteRatio cut χ finest dimension' Kcap : ℝ}
    (data : (a : Fin p.C) → Fp.active a → OriginalAncestorRecordSource Fp a
      (C.current (p.γ a) ∩ p.F a) (coreK p τ) baseRef hiddenRef pv paletteRatio cut rF frF χ
        finest dimension' Kcap)
    (K2 : Fin (d.W k) → Set Ev) (hK2 : ∀ w, MeasurableSet (K2 w) ∧ K2 w ⊆ C.current w)
    (hK2slice : ∀ a (ha : Fp.active a), K2 (p.γ a) ∩ p.F a = (data a ha).kept)
    -- the per-sample scalars
    (c : ℕ) {K θ ε aA q d₁ : ℝ}
    (hqaA : q / aA = ((2 : ℝ) ^ p.T i)⁻¹ / Parent.ParentSource.δ (d.N k) (p.r i))
    -- the census of every active root (x1065's theorem, via x1088's root_census_package)
    (hmidfam : ∀ j : Fin nfam, i + (j : ℕ) ≤ stop) (hrfam : ∀ j : Fin nfam, 0 ≤ p.r (i + (j : ℕ)))
    (hrLfam : ∀ j : Fin nfam, p.r (i + (j : ℕ)) ≤ d.L)
    (hwidthfam : ∀ j : Fin nfam,
      Parent.ParentSource.δ (d.N k) (p.r (i + (j : ℕ))) ≤ Parent.ParentSource.δ (d.N k) (p.r i))
    {Kc width θrow : ℝ} {qc : ℕ}
    (hKc : 2 * coreK p τ ^ ((3 * FixedSourcePowers.coreRadius + 58) + 7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc ^ qc)⁻¹ ≤ width)
    (hstrip : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ rF)
    (hdeep : ∀ j : Fin nfam, ∀ fine deep : Fin p.C, p.lev fine = i + (j : ℕ) → p.lev deep = stop →
      6 * coreK p τ ^ FixedSourcePowers.coreRadius * p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤
        renewalCellMesh Kc FixedSourcePowers.jet qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ frF)
    (δref : ENNReal) (hδ0 : δref ≠ 0) (hδtop : δref ≠ ∞)
    (hβ1 : δref⁻¹ * ENNReal.ofReal (8 * frF) < 1)
    {Kgeom : ℝ} (hKK : coreK p τ ≤ Kgeom)
    (hgeometry : d.N k ^ (2 * δ₀ * d.L) ≤ Kgeom) (hconstant : 96 * coreRowK₀ ≤ Kgeom)
    (w t : ℕ) (hwidthPower : (Kgeom ^ w)⁻¹ ≤ width) (hθPower : (Kgeom ^ t)⁻¹ ≤ θrow)
    (hκ₁ : κ₁ ≤ 1) (hmidm : ∀ j : Fin nfam, i + (j : ℕ) < m)
    (nnA : ℕ) (indexA : Fin nnA → Fin nfam) (hmatchA : ∀ j, (indexA j : ℕ) = j.val + 1)
    (hsA : ∀ j : Fin nnA, s i ≤ s (i + (j.val + 1)))
    (dimension profileErrorA fineMeshA KcensusA : ℝ) (gapPowerA : ℕ)
    (hdim0 : 0 ≤ dimension) (hdim1 : dimension < 1)
    (hprofileA : ∀ j : Fin nnA, d.f (p.r (i + (j.val + 1))) - d.f (p.r i) ≤
      dimension * (p.r (i + (j.val + 1)) - p.r i) + profileErrorA)
    (hprofilePowerA : d.N k ^ profileErrorA ≤ Kgeom) (hFineA : 0 < fineMeshA)
    (hθKA : (Parent.ParentSource.δ (d.N k) (p.r i) / Parent.ParentSource.δ (d.N k) (p.r i)) /
      ((2 : ℝ) ^ p.T i / (2 : ℝ) ^ p.T i) ≤ KcensusA)
    (hbudgetA : Kgeom ^ (3 * FixedSourcePowers.coreRadius + (((3 * FixedSourcePowers.coreRadius + 58)
      + 8) * FixedSourcePowers.jet + w + t * ⌈coreRowC₀⌉₊ + 1) + gapPowerA + 83) ≤ KcensusA)
    (hlastA : Kgeom ^ ((((3 * FixedSourcePowers.coreRadius + 58) + 8) * FixedSourcePowers.jet + w +
        t * ⌈coreRowC₀⌉₊ + 1) + 10) *
      (Parent.ParentSource.δ (d.N k) (p.r (i + nnA)) / Parent.ParentSource.δ (d.N k) (p.r i)) ≤
        fineMeshA)
    (hstepA : ∀ j < nnA, Parent.ParentSource.δ (d.N k) (p.r (i + j)) /
        Parent.ParentSource.δ (d.N k) (p.r i) ≤
      Kgeom ^ gapPowerA * (Parent.ParentSource.δ (d.N k) (p.r (i + (j + 1))) /
        Parent.ParentSource.δ (d.N k) (p.r i)))
    (nnB : ℕ) (indexB : Fin nnB → Fin nfam) (hmatchB : ∀ j, (indexB j : ℕ) = c + j.val + 1)
    (hsB : ∀ j : Fin nnB, s (i + c) ≤ s (i + c + (j.val + 1)))
    (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1) (profileErrorB fineMeshB KcensusB : ℝ) (gapPowerB : ℕ)
    (hprofileB : ∀ j : Fin nnB, d.f (p.r (i + c + (j.val + 1))) - d.f (p.r (i + c)) ≤
      d₁ * (p.r (i + c + (j.val + 1)) - p.r (i + c)) + profileErrorB)
    (hprofilePowerB : d.N k ^ profileErrorB ≤ Kgeom) (hFineB : 0 < fineMeshB)
    (hθKB : (Parent.ParentSource.δ (d.N k) (p.r (i + c)) / Parent.ParentSource.δ (d.N k) (p.r i)) /
      ((2 : ℝ) ^ p.T i / (2 : ℝ) ^ p.T (i + c)) ≤ KcensusB)
    (hbudgetB : Kgeom ^ (3 * FixedSourcePowers.coreRadius + (((3 * FixedSourcePowers.coreRadius + 58)
      + 8) * FixedSourcePowers.jet + w + t * ⌈coreRowC₀⌉₊ + 1) + gapPowerB + 83) ≤ KcensusB)
    (hlastB : Kgeom ^ ((((3 * FixedSourcePowers.coreRadius + 58) + 8) * FixedSourcePowers.jet + w +
        t * ⌈coreRowC₀⌉₊ + 1) + 10) *
      (Parent.ParentSource.δ (d.N k) (p.r (i + c + nnB)) /
        Parent.ParentSource.δ (d.N k) (p.r (i + c))) ≤ fineMeshB)
    (hstepB : ∀ j < nnB, Parent.ParentSource.δ (d.N k) (p.r (i + c + j)) /
        Parent.ParentSource.δ (d.N k) (p.r (i + c)) ≤
      Kgeom ^ gapPowerB * (Parent.ParentSource.δ (d.N k) (p.r (i + c + (j + 1))) /
        Parent.ParentSource.δ (d.N k) (p.r (i + c))))
    (hTlb : p.T i ≤ p.T (i + c))
    (hscale : O204.Split.δ (d.N k) (p.r (i + c)) ≤ O204.Split.δ (d.N k) (p.r i))
    (hr0 : 0 ≤ p.r (i + c)) (hrLb : p.r (i + c) ≤ d.L)
    (hprof : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L)
    (hε : 0 < ε) (hres : d.N k ^ (-(d.L - p.r (i + c))) ≤ 4 * ε)
    (hKbase : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * d.N k ^ (τ + 2 * δ₀ * d.L + τ) ≤ K)
    (hKband : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
      d.N k ^ (2 * (δ₀ * d.L) + (τ + 2 * δ₀ * d.L) + τ) ≤ K)
    (hKc1 : 1 ≤ KcensusB) (hKcK : KcensusB ≤ K) (hfine : fineMeshB ≤ ε)
    -- the velocity bound, the MK4 rows, the renewal and the band
    {Vmax : ℝ} (hV0 : 0 ≤ Vmax) (hvel : ∀ w, ∀ z ∈ Rp.residual w, ‖Parent.v z.1‖ ≤ Vmax)
    {cellRate durationRate coarse radius ratio : ℝ} (steps : ℕ)
    (hFine1 : fineMeshA ≤ 1) (hKcensus : 1 ≤ KcensusA)
    (hsteps : KcensusA ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps)
    (hresolved : fineMeshA * (2 : ℝ) ^ steps ≤ 1)
    (hcellRate : 0 < cellRate) (hdurationRate : 0 < durationRate) (hratio0 : 0 ≤ ratio)
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hcut : 0 < cut)
    (hbaseBudget : 3 * baseRef ≤ fineMeshA * (2 : ℝ) ^ steps)
    (hhiddenBudget : 3 * hiddenRef ≤ fineMeshA * (2 : ℝ) ^ steps)
    (betaR : ENNReal) (hbetaR : betaR ≠ 0) (hbetaRTop : betaR ≠ ⊤)
    (hwidthR : (6 * p.κ) * radius ≤ rF)
    (hratio : ENNReal.ofReal ((8 * frF) / cut) / betaR ≤ ENNReal.ofReal ratio)
    (hri : 0 ≤ p.r i) (hrLi : p.r i ≤ d.L)
    {f₀ perror : ℝ} (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - f₀ - dimension * r| ≤ perror)
    (nmesh : ℕ) (hmesh : fineMeshA * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh nmesh)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse nmesh)
    (hbandResolved : d.N k ^ (-(d.L - p.r i)) ≤ 4 * coarse)
    {Kg baseRho wMK gfraction εMK : ℝ}
    (hKgJ : 6 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) ≤ Kg) (hKgRate : durationRate⁻¹ ≤ Kg)
    (hKgCount : 8 * (64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
      d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + τ)) / cellRate ≤ Kg)
    (hbaseRho : 0 ≤ baseRho) (hcond : 1 ≤ Kg * baseRho ^ 3) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (Vmax + 1) * baseRho ≤ wMK)
    (hwRadius : wMK * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (hgfraction : 0 < gfraction) (hgfrac : gfraction < 1 - ratio) (hεMK : 0 < εMK)
    (hsmall : Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24) ≤
      min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
        ((gfraction / 4) ^ 4 * εMK ^ 4 /
          (256 * Parent.ParentSource.Broad.Velocity.curvatureRowConstant ^ 3 * Kg ^ 9 + 1))))
    (hθ80 : 80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24) ≤
      θ) :
    ∃ RP : RootPackage Qp Fp Rp c K θ ε aA q d₁ (hRelOf (p.T i) (p.T (i + c)))
        (aRelOf (d.N k) (p.r i) (p.r (i + c))) (coreK p τ) baseRef hiddenRef pv paletteRatio cut
        rF frF χ finest dimension' Kcap C,
      RP.graphMesh = Submission.Lib.K4DyadicRowScales.mesh nmesh ∧ RP.Brow = 28 * Kg ^ 6 ∧
      (∀ a, Fp.active a → ∀ x ∈ RP.E1 (p.γ a) ∩ p.F a,
        |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
          ∑ j : Fin 3, RP.row a (ancCode (d.N k) p a RP.graphMesh x) j *
            (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤
        80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24)) ∧
      (∀ a, Fp.active a → ∀ b w : ℝ, fineMeshA ≤ b → b ≤ 1 → fineMeshA ≤ w → w ≤ 1 →
        KcensusA ^ (100 : ℕ) * b ≤ 1 * w →
        (occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
        ((occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
          KcensusA / (b ^ 3 * w ^ dimension)) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (K2 w)) ≤
        ENNReal.ofReal (1 - gfraction)⁻¹ *
          (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w)) +
        ((nfam : ENNReal) * (ENNReal.ofReal (4 * coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 28) *
            p.κ ^ 2) * (ENNReal.ofReal (θrow * (coreK p τ ^ FixedSourcePowers.coreRadius)⁻¹) +
              27 * (δref * ENNReal.ofReal (p.κ ^ 2)))) +
          (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal εMK +
            (ENNReal.ofReal ((KcensusA * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
              ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
                (7 : ℝ) ^ 4)) + 81 * betaR)) := by
  have hN1 : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hκ1 : 1 ≤ p.κ := hp.1
  obtain ⟨hK2304, hκK, hmax, hpower⟩ :=
    Submission.Lib.K4NativePreparationNumerics.native_pre_geometry_envelope_bounds
      (source := d.K k) hκ1 hN1 (by linarith : 0 ≤ τ + τ)
  have hresE : ∀ w, Rp.residual w ⊆ d.E k w := fun w z hz => hHE w (Rp.subset_H w hz)
  have hresB : ∀ w, Rp.residual w ⊆ Qp.base w := fun w => broadResidual_subset_base Rp w
  -- the census of every active root
  have hcensusRoot : ∀ a (ha : Fp.active a), ∃ current : Set Ev, MeasurableSet current ∧
      current ⊆ (data a ha).kept ∧
      ((d.ν k (p.γ a)).prod volume) (data a ha).kept ≤ ((d.ν k (p.γ a)).prod volume) current +
        ((nfam : ENNReal) * (ENNReal.ofReal (4 * coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 28) *
            p.κ ^ 2) * (ENNReal.ofReal (θrow * (coreK p τ ^ FixedSourcePowers.coreRadius)⁻¹) +
              27 * (δref * ENNReal.ofReal (p.κ ^ 2))))) *
          (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) ∧
      (∀ b w : ℝ, fineMeshA ≤ b → b ≤ 1 → fineMeshA ≤ w → w ≤ 1 →
        KcensusA ^ (100 : ℕ) * b ≤ 1 * w →
        (occupied current (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
        ((occupied current (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
          KcensusA / (b ^ 3 * w ^ dimension)) ∧
      ∀ b, p.lev b = i + c → p.par^[c] b = a → ∀ Se : Set Ev, MeasurableSet Se →
        Se ⊆ current ∩ p.F b →
        CapClauses K ε d₁ (hRelOf (p.T i) (p.T (i + c))) (aRelOf (d.N k) (p.r i) (p.r (i + c)))
          (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
          (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
          (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
            O204.Split.δ (d.N k) (p.r (p.lev b))) Se := by
    intro a ha
    have hla : p.lev a = i := Fp.level a ha
    have hkeptSub : (data a ha).kept ⊆ C.current (p.γ a) ∩ p.F a := (data a ha).kept_subset
    subst hla
    obtain ⟨current, hcm, hcsub, hcmass, hcMK4, hcCaps⟩ := root_census_package Qp hpure hd hp C
      hresE hresB hH hK2304 hmax hpower hκK Rp (fun _ => subset_rfl) a rfl ha
      (fun j => Nat.le_add_right _ _) hmidfam hrfam hrLfam (le_refl 5186)
      FixedSourcePowers.jet_bound hwidthfam hKc hwidthpos
      hwidthfloor hstrip hdeep hθrow hθrow1 hfraction δref hδ0 hδtop hβ1 (data a ha).kept
      (data a ha).kept_measurable hkeptSub hKK hgeometry hconstant w t hwidthPower hθPower hκ₁
      hmidm nnA (fun l => p.lev a + l) indexA rfl (fun j => by simp only [hmatchA j])
      (fun j => Nat.le_add_right _ _) hsA dimension profileErrorA fineMeshA KcensusA gapPowerA
      hdim0 hdim1.le hprofileA hprofilePowerA hFineA hθKA hbudgetA hlastA hstepA
      c (p.lev a + c) rfl nnB (fun l => p.lev a + c + l) indexB rfl
      (fun j => by simp only [hmatchB j]; omega)
      (fun j => Nat.le_add_right _ _) hsB hd₀ hd₁ profileErrorB fineMeshB KcensusB gapPowerB
      hprofileB hprofilePowerB hFineB hθKB hbudgetB hlastB hstepB hTlb hscale hr0 hrLb hprof hε
      hres hKbase hKband hKc1 hKcK hfine
    refine ⟨current, hcm, hcsub, hcmass, hcMK4, fun b hb hab Se hSe hSeSub => ?_⟩
    have h := hcCaps b hb hab Se hSe hSeSub
    rw [hab]
    exact h
  exact rootPackage_exists Qp hpure hd hp hHE hH (c := c) (K := K) (θ := θ) (ε := ε) (aA := aA)
    (q := q) (d₁ := d₁) hqaA C (fun w => C.current_subset w) data K2 hK2 hK2slice hV0 hvel
    hcensusRoot steps hFineA hFine1 hKcensus hsteps hresolved hcellRate hdurationRate hratio0
    hbaseRef hhiddenRef hcut hfraction hbaseBudget hhiddenBudget betaR hbetaR hbetaRTop hwidthR
    hratio hri hrLi hprofile nmesh hmesh hcoarse hbandResolved hdim0 hdim1 hKgJ hKgRate hKgCount
    hbaseRho hcond hbaseRho4 hwRho hwRadius hgfraction hgfrac hεMK hsmall hθ80

open Submission.Lib.K4ParentSignalPreparation.Census in
/-- **The core source, the records and the root package of a sample**, with the mass chain from
the broad residual to the root survivors. -/
theorem sample_package (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {H : Fin (d.W k) → Set Ev} (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {τ : ℝ} (hτ : 0 ≤ τ) (Qp : PreparedAngularPath d k p m H (fun _ : Fin 1 => d.η * d.L) τ)
    (hpure : Qp.uniformPureBounds τ)
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} (Fp : PaletteFamily Qp i stop meshF envF θF)
    {rF frF : ℝ} (Rp : BroadResidual Fp rF frF)
    -- the core depth family
    (nfam : ℕ) (hdepth : ∀ j : Fin nfam, i + (j : ℕ) < m)
    (hr : ∀ j : Fin nfam, 0 ≤ p.r (i + (j : ℕ))) (hrL : ∀ j : Fin nfam, p.r (i + (j : ℕ)) ≤ d.L)
    (hn : (nfam : ℝ) ≤ Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ))
    -- the record depth and the record numerics
    (jrec : Fin nfam) (hjstop : i + (jrec : ℕ) ≤ stop)
    (hwidthrec : δ (d.N k) (p.r (i + (jrec : ℕ))) ≤ δ (d.N k) (p.r i))
    {baseRef hiddenRef : ℝ} (hbase : 0 < baseRef) (hhidden : 0 < hiddenRef)
    (hbaseSmall : ∀ root : Fin p.C, p.lev root = i → ∀ deep : Fin p.C, p.lev deep = stop →
      p.unshearedDeepRadius root deep ≤ baseRef)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine = i + (jrec : ℕ) → p.lev deep = stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤
        (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^
          FixedSourcePowers.coreRadius)⁻¹ / 12)
    (hheightSmall : ∀ root : Fin p.C, p.lev root = i →
      ∀ fine deep : Fin p.C, p.lev fine = i + (jrec : ℕ) → p.lev deep = stop →
      (δ (d.N k) (p.r (p.lev root)) / δ (d.N k) (p.r (p.lev root))) *
        (2 * (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^ 14 *
          (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^ 6)⁻¹ *
          (δ (d.N k) (p.r (i + (jrec : ℕ))) / δ (d.N k) (p.r (p.lev root)))) +
          ((Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^
              ((3 * FixedSourcePowers.coreRadius + 58) + 7)) ^ FixedSourcePowers.jet *
            (p.κ + Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^ 14 *
              (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^ 6)⁻¹)) *
            (6 * Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^
              FixedSourcePowers.coreRadius * p.deepBaseRadius (d.N k) d.L δ₀ fine deep)) ≤
        hiddenRef)
    (pv paletteRatio : ℝ) (hRatio : 0 ≤ paletteRatio)
    (hOriginal : ∀ b, Fp.active b → Fp.U b ⊆ likelihoodGood Qp.law (labelledSupport Qp.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette pv) i stop paletteRatio)
    (χ finest : ℝ) (hχ : 0 ≤ χ)
    {dimension' f₀ profileError Kcap : ℝ} (hdim : 0 ≤ dimension')
    (hprofileRec : ∀ x, 0 ≤ x → x ≤ d.L → |d.f x - f₀ - dimension' * x| ≤ profileError)
    (hbudget : 512 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension' *
      d.N k ^ (2 * profileError + (τ + 2 * δ₀ * d.L) + τ) ≤ Kcap)
    (cut : ℝ) (hcut : 0 < cut)
    -- the per-sample scalars
    (c : ℕ) {K θ ε aA q d₁ : ℝ}
    (hqaA : q / aA = ((2 : ℝ) ^ p.T i)⁻¹ / Parent.ParentSource.δ (d.N k) (p.r i))
    -- the census of every active root (x1065's theorem, via x1088's root_census_package)
    (hmidfam : ∀ j : Fin nfam, i + (j : ℕ) ≤ stop)     (hwidthfam : ∀ j : Fin nfam,
      Parent.ParentSource.δ (d.N k) (p.r (i + (j : ℕ))) ≤ Parent.ParentSource.δ (d.N k) (p.r i))
    {Kc width θrow : ℝ} {qc : ℕ}
    (hKc : 2 * coreK p τ ^ ((3 * FixedSourcePowers.coreRadius + 58) + 7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc ^ qc)⁻¹ ≤ width)
    (hstrip : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ rF)
    (hdeep : ∀ j : Fin nfam, ∀ fine deep : Fin p.C, p.lev fine = i + (j : ℕ) → p.lev deep = stop →
      6 * coreK p τ ^ FixedSourcePowers.coreRadius * p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤
        renewalCellMesh Kc FixedSourcePowers.jet qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ frF)
    (δref : ENNReal) (hδ0 : δref ≠ 0) (hδtop : δref ≠ ∞)
    (hβ1 : δref⁻¹ * ENNReal.ofReal (8 * frF) < 1)
    {Kgeom : ℝ} (hKK : coreK p τ ≤ Kgeom)
    (hgeometry : d.N k ^ (2 * δ₀ * d.L) ≤ Kgeom) (hconstant : 96 * coreRowK₀ ≤ Kgeom)
    (w t : ℕ) (hwidthPower : (Kgeom ^ w)⁻¹ ≤ width) (hθPower : (Kgeom ^ t)⁻¹ ≤ θrow)
    (hκ₁ : κ₁ ≤ 1)
    (nnA : ℕ) (indexA : Fin nnA → Fin nfam) (hmatchA : ∀ j, (indexA j : ℕ) = j.val + 1)
    (hsA : ∀ j : Fin nnA, s i ≤ s (i + (j.val + 1)))
    (dimension profileErrorA fineMeshA KcensusA : ℝ) (gapPowerA : ℕ)
    (hdim0 : 0 ≤ dimension) (hdim1 : dimension < 1)
    (hprofileA : ∀ j : Fin nnA, d.f (p.r (i + (j.val + 1))) - d.f (p.r i) ≤
      dimension * (p.r (i + (j.val + 1)) - p.r i) + profileErrorA)
    (hprofilePowerA : d.N k ^ profileErrorA ≤ Kgeom) (hFineA : 0 < fineMeshA)
    (hθKA : (Parent.ParentSource.δ (d.N k) (p.r i) / Parent.ParentSource.δ (d.N k) (p.r i)) /
      ((2 : ℝ) ^ p.T i / (2 : ℝ) ^ p.T i) ≤ KcensusA)
    (hbudgetA : Kgeom ^ (3 * FixedSourcePowers.coreRadius + (((3 * FixedSourcePowers.coreRadius + 58)
      + 8) * FixedSourcePowers.jet + w + t * ⌈coreRowC₀⌉₊ + 1) + gapPowerA + 83) ≤ KcensusA)
    (hlastA : Kgeom ^ ((((3 * FixedSourcePowers.coreRadius + 58) + 8) * FixedSourcePowers.jet + w +
        t * ⌈coreRowC₀⌉₊ + 1) + 10) *
      (Parent.ParentSource.δ (d.N k) (p.r (i + nnA)) / Parent.ParentSource.δ (d.N k) (p.r i)) ≤
        fineMeshA)
    (hstepA : ∀ j < nnA, Parent.ParentSource.δ (d.N k) (p.r (i + j)) /
        Parent.ParentSource.δ (d.N k) (p.r i) ≤
      Kgeom ^ gapPowerA * (Parent.ParentSource.δ (d.N k) (p.r (i + (j + 1))) /
        Parent.ParentSource.δ (d.N k) (p.r i)))
    (nnB : ℕ) (indexB : Fin nnB → Fin nfam) (hmatchB : ∀ j, (indexB j : ℕ) = c + j.val + 1)
    (hsB : ∀ j : Fin nnB, s (i + c) ≤ s (i + c + (j.val + 1)))
    (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1) (profileErrorB fineMeshB KcensusB : ℝ) (gapPowerB : ℕ)
    (hprofileB : ∀ j : Fin nnB, d.f (p.r (i + c + (j.val + 1))) - d.f (p.r (i + c)) ≤
      d₁ * (p.r (i + c + (j.val + 1)) - p.r (i + c)) + profileErrorB)
    (hprofilePowerB : d.N k ^ profileErrorB ≤ Kgeom) (hFineB : 0 < fineMeshB)
    (hθKB : (Parent.ParentSource.δ (d.N k) (p.r (i + c)) / Parent.ParentSource.δ (d.N k) (p.r i)) /
      ((2 : ℝ) ^ p.T i / (2 : ℝ) ^ p.T (i + c)) ≤ KcensusB)
    (hbudgetB : Kgeom ^ (3 * FixedSourcePowers.coreRadius + (((3 * FixedSourcePowers.coreRadius + 58)
      + 8) * FixedSourcePowers.jet + w + t * ⌈coreRowC₀⌉₊ + 1) + gapPowerB + 83) ≤ KcensusB)
    (hlastB : Kgeom ^ ((((3 * FixedSourcePowers.coreRadius + 58) + 8) * FixedSourcePowers.jet + w +
        t * ⌈coreRowC₀⌉₊ + 1) + 10) *
      (Parent.ParentSource.δ (d.N k) (p.r (i + c + nnB)) /
        Parent.ParentSource.δ (d.N k) (p.r (i + c))) ≤ fineMeshB)
    (hstepB : ∀ j < nnB, Parent.ParentSource.δ (d.N k) (p.r (i + c + j)) /
        Parent.ParentSource.δ (d.N k) (p.r (i + c)) ≤
      Kgeom ^ gapPowerB * (Parent.ParentSource.δ (d.N k) (p.r (i + c + (j + 1))) /
        Parent.ParentSource.δ (d.N k) (p.r (i + c))))
    (hTlb : p.T i ≤ p.T (i + c))
    (hscale : O204.Split.δ (d.N k) (p.r (i + c)) ≤ O204.Split.δ (d.N k) (p.r i))
    (hr0 : 0 ≤ p.r (i + c)) (hrLb : p.r (i + c) ≤ d.L)
    (hprof : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L)
    (hε : 0 < ε) (hres : d.N k ^ (-(d.L - p.r (i + c))) ≤ 4 * ε)
    (hKbase : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * d.N k ^ (τ + 2 * δ₀ * d.L + τ) ≤ K)
    (hKband : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
      d.N k ^ (2 * (δ₀ * d.L) + (τ + 2 * δ₀ * d.L) + τ) ≤ K)
    (hKc1 : 1 ≤ KcensusB) (hKcK : KcensusB ≤ K) (hfine : fineMeshB ≤ ε)
    -- the velocity bound, the MK4 rows, the renewal and the band
    {Vmax : ℝ} (hV0 : 0 ≤ Vmax) (hvel : ∀ w, ∀ z ∈ Rp.residual w, ‖Parent.v z.1‖ ≤ Vmax)
    {cellRate durationRate coarse radius ratio : ℝ} (steps : ℕ)
    (hFine1 : fineMeshA ≤ 1) (hKcensus : 1 ≤ KcensusA)
    (hsteps : KcensusA ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps)
    (hresolved : fineMeshA * (2 : ℝ) ^ steps ≤ 1)
    (hcellRate : 0 < cellRate) (hdurationRate : 0 < durationRate) (hratio0 : 0 ≤ ratio)
    (hbaseBudget : 3 * baseRef ≤ fineMeshA * (2 : ℝ) ^ steps)
    (hhiddenBudget : 3 * hiddenRef ≤ fineMeshA * (2 : ℝ) ^ steps)
    (betaR : ENNReal) (hbetaR : betaR ≠ 0) (hbetaRTop : betaR ≠ ⊤)
    (hwidthR : (6 * p.κ) * radius ≤ rF)
    (hratio : ENNReal.ofReal ((8 * frF) / cut) / betaR ≤ ENNReal.ofReal ratio)
    (hri : 0 ≤ p.r i) (hrLi : p.r i ≤ d.L)
    {f₀' perror : ℝ} (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - f₀' - dimension * r| ≤ perror)
    (nmesh : ℕ) (hmesh : fineMeshA * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh nmesh)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse nmesh)
    (hbandResolved : d.N k ^ (-(d.L - p.r i)) ≤ 4 * coarse)
    {Kg baseRho wMK gfraction εMK : ℝ}
    (hKgJ : 6 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) ≤ Kg) (hKgRate : durationRate⁻¹ ≤ Kg)
    (hKgCount : 8 * (64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
      d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + τ)) / cellRate ≤ Kg)
    (hbaseRho : 0 ≤ baseRho) (hcond : 1 ≤ Kg * baseRho ^ 3) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (Vmax + 1) * baseRho ≤ wMK)
    (hwRadius : wMK * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (hgfraction : 0 < gfraction) (hgfrac : gfraction < 1 - ratio) (hεMK : 0 < εMK)
    (hsmall : Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24) ≤
      min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
        ((gfraction / 4) ^ 4 * εMK ^ 4 /
          (256 * Parent.ParentSource.Broad.Velocity.curvatureRowConstant ^ 3 * Kg ^ 9 + 1))))
    (hθ80 : 80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24) ≤
      θ) :
    ∃ (C : BroadMultiscaleCoreSource d k p Rp.residual nfam (fun j => i + (j : ℕ)) (coreK p τ)
        FixedSourcePowers.coreE FixedSourcePowers.coreRadius)
      (RP : RootPackage Qp Fp Rp c K θ ε aA q d₁ (hRelOf (p.T i) (p.T (i + c)))
        (aRelOf (d.N k) (p.r i) (p.r (i + c))) (coreK p τ) baseRef hiddenRef pv paletteRatio cut
        rF frF χ finest dimension' Kcap C),
      RP.graphMesh = Submission.Lib.K4DyadicRowScales.mesh nmesh ∧ RP.Brow = 28 * Kg ^ 6 ∧
      (∀ a, Fp.active a → ∀ x ∈ RP.E1 (p.γ a) ∩ p.F a,
        |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
          ∑ j : Fin 3, RP.row a (ancCode (d.N k) p a RP.graphMesh x) j *
            (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤
        80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24)) ∧
      (∀ a, Fp.active a → ∀ b w : ℝ, fineMeshA ≤ b → b ≤ 1 → fineMeshA ≤ w → w ≤ 1 →
        KcensusA ^ (100 : ℕ) * b ≤ 1 * w →
        (occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
        ((occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
          KcensusA / (b ^ 3 * w ^ dimension)) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w)) ≤
        ENNReal.ofReal (1 - gfraction)⁻¹ *
          (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w)) +
        ((nfam : ENNReal) * (ENNReal.ofReal (4 * coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 28) *
            p.κ ^ 2) * (ENNReal.ofReal (θrow * (coreK p τ ^ FixedSourcePowers.coreRadius)⁻¹) +
              27 * (δref * ENNReal.ofReal (p.κ ^ 2)))) +
          (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal εMK +
            (ENNReal.ofReal ((KcensusA * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
              ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
                (7 : ℝ) ^ 4)) + 81 * betaR)) +
        ENNReal.ofReal cut * (⌈coreK p τ ^ 12⌉₊ : ENNReal) + ENNReal.ofReal (p.κ⁻¹ / 64) := by
  obtain ⟨C, data, K2, hK2, hK2slice, hmass1⟩ := sample_core_records hd hp hHE hH hτ Qp hpure Fp
    Rp nfam hdepth hr hrL hn jrec hjstop hwidthrec hbase hhidden hbaseSmall hcoreSmall
    hheightSmall pv paletteRatio hRatio hOriginal χ finest hχ hdim hprofileRec hbudget cut hcut
  obtain ⟨RP, hmesh', hB', hfit', hocc', hmass2⟩ := sample_root_package hd hp hHE hH hτ Qp hpure
    Fp Rp C data K2 hK2 hK2slice c hqaA hmidfam hr hrL hwidthfam hKc hwidthpos hwidthfloor hstrip
    hdeep hθrow hθrow1 hfraction δref hδ0 hδtop hβ1 hKK hgeometry hconstant w t hwidthPower
    hθPower hκ₁ hdepth nnA indexA hmatchA hsA dimension profileErrorA fineMeshA KcensusA
    gapPowerA hdim0 hdim1 hprofileA hprofilePowerA hFineA hθKA hbudgetA hlastA hstepA nnB indexB
    hmatchB hsB hd₀ hd₁ profileErrorB fineMeshB KcensusB gapPowerB hprofileB hprofilePowerB
    hFineB hθKB hbudgetB hlastB hstepB hTlb hscale hr0 hrLb hprof hε hres hKbase hKband hKc1 hKcK
    hfine hV0 hvel steps hFine1 hKcensus hsteps hresolved hcellRate hdurationRate hratio0 hbase
    hhidden hcut hbaseBudget hhiddenBudget betaR hbetaR hbetaRTop hwidthR hratio hri hrLi hprofile
    nmesh hmesh hcoarse hbandResolved hKgJ hKgRate hKgCount hbaseRho hcond hbaseRho4 hwRho
    hwRadius hgfraction hgfrac hεMK hsmall hθ80
  refine ⟨C, RP, hmesh', hB', hfit', hocc', ?_⟩
  calc (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w))
      ≤ (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (K2 w)) +
          ENNReal.ofReal cut * (⌈coreK p τ ^ 12⌉₊ : ENNReal) + ENNReal.ofReal (p.κ⁻¹ / 64) := hmass1
    _ ≤ _ := add_le_add (add_le_add hmass2 le_rfl) le_rfl

end Sample

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
