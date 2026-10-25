-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleFinal, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRoot

/-!
# One sample of the relative source, end to end (session x1082)

`sample_final`: at one sample of the front (prepared path `Qp`, palette family `Fp`, broad residual
`Rp`), the core source and the records (`sample_core_records`), the root package
(`sample_root_package`), the native root preparation of x1096 (input `hnative`: a per-root cut of the
root package with a full-reference charge, and the regularity/qualification input `SampleHbox` on
the restricted package) and the post-state stages (`samplePost_of_rootPackage`) give the literal
`StagesProducer` existential at this sample, from scalar hypotheses only (and `hnative`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual
  likelihoodGood labelledSupport finitePacketHistory labelledVelocityPalette)
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal

noncomputable section

section Sample

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

/-- **One sample, end to end.** -/
theorem sample_final (hd : d.Valid)
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
      θ)
    -- the record/state numerics
    (hfinePv : 0 < pv) {pvP : ℝ} (hpvP : pv ≤ pvP)
    (hgraphBase : 3 * baseRef ≤ Submission.Lib.K4DyadicRowScales.mesh nmesh)
    (hgraphHidden : 3 * hiddenRef ≤ Submission.Lib.K4DyadicRowScales.mesh nmesh)
    (hphysicalBase : ∀ b, p.lev b = i + c →
      3 * ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev (p.par^[c] b))) * baseRef ≤ ε)
    (hphysicalHidden : ∀ b, p.lev b = i + c →
      3 * (δ (d.N k) (p.r (p.lev (p.par^[c] b))) / δ (d.N k) (p.r (p.lev b))) * hiddenRef ≤
        (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev b))) * ε)
    (beta : ENNReal) (hbeta : beta ≠ 0) (hbetaTop : beta ≠ ⊤)
    (hstripWidth : ∀ b, p.lev b = i + c →
      (K / 4) ^ (-100 : ℝ) * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (p.par^[c] b) j l|) ≤
        rF * ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)) * |(p.Q (p.par^[c] b)).det|))
    (hstripRatio : ENNReal.ofReal ((8 * frF) / cut) / beta ≤ (1 / 2000000000000 : ENNReal))
    (hpaletteRatio : ENNReal.ofReal ((8 * paletteRatio) / cut) / beta ≤ ENNReal.ofReal (K / 4))
    (hBK : 28 * Kg ^ 6 ≤ K)
    (radiusP stripWidth : ℝ) (hNormalizedWidth : (6 * p.κ) * radiusP ≤ rF)
    (hOriginalWidth : ∀ b, p.lev b = i + c →
      stripWidth * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (p.par^[c] b) j l|) ≤
        rF * ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)) * |(p.Q (p.par^[c] b)).det|))
    -- the regularity/qualification stage on the post-state slices
    (Mq Tq : ℕ) (qmesh qerror qduration : ℝ) (qbound : ℤ)
    (Pfac chargeR η : ENNReal) (hPfac : Pfac ≠ ⊤) (hPfac0 : Pfac ≠ 0) (hchargeR : chargeR ≠ ⊤)
    (hη : η ≠ ⊤) {Lp ρ : ℝ} (hLp : 0 ≤ Lp)
    -- the lists at the middle depth of the core source
    (jmid : Fin nfam) (hmidb : ∀ b, p.lev b = i + c → (i + (jmid : ℕ)) ≤ p.lev b)
    (hmida : ∀ b, p.lev b = i + c → p.lev b - c ≤ (i + (jmid : ℕ)))
    (hrmid : 0 ≤ p.r ((i + (jmid : ℕ)))) (hrLmid : p.r ((i + (jmid : ℕ))) ≤ d.L)
    (hwidthmid : δ (d.N k) (p.r ((i + (jmid : ℕ)))) ≤ δ (d.N k) (p.r i))
    (hsmallList : ∀ b, p.lev b = i + c →
      ((aA / q) * Lp) * ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
          ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)))⁻¹) * (2 * θ) +
        (2 * (coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹ * (δ (d.N k) (p.r ((i + (jmid : ℕ)))) /
          δ (d.N k) (p.r (p.lev (p.par^[c] b))))) +
          ((coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 58 + 7)) ^ FixedSourcePowers.jet * (p.κ + coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹)) *
            (coreK p τ ^ FixedSourcePowers.coreRadius * ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
              ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
                ((2 : ℝ) ^ p.T (p.lev (p.par^[p.lev b - (i + (jmid : ℕ))] b)))⁻¹) * (6 * θ))))) +
        ρ) ≤ (aA / q) * θ)
    (hcount : (coreK p τ ^ 10 * (2 * coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 18))) * 9 ^ 3 ≤ K)
    -- the qualification numerics
    (hqmesh : 0 ≤ qmesh) (hqbound : 0 ≤ qbound)
    (hcoeff : Parent.QualificationClock.coefficientCost Mq * (qmesh * qbound) ≤ K)
    (herror : qerror ≤ θ)
    (hduration : ∀ b, p.lev b = i + c → 1 / K ≤ qduration / ((((2 : ℝ) ^ p.T (p.lev b))⁻¹) /
      (((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)))⁻¹)))
    -- the levels and the positivity of the scalars
    (hibm : i + c ≤ m - 1) (hcstop : i + c ≤ stop) (hKpos : 0 < K) (hθpos : 0 < θ)
    (haApos : 0 < aA) (hqpos : 0 < q)
    -- the native root preparation and its regularity/qualification input (x1096)
    {chargeN : ENNReal} (hchargeN : chargeN ≠ ⊤)
    (hnative : ∀ (C : BroadMultiscaleCoreSource d k p Rp.residual nfam (fun j => i + (j : ℕ))
        (coreK p τ) FixedSourcePowers.coreE FixedSourcePowers.coreRadius)
      (RP : RootPackage Qp Fp Rp c K θ ε aA q d₁ (hRelOf (p.T i) (p.T (i + c)))
        (aRelOf (d.N k) (p.r i) (p.r (i + c))) (coreK p τ) baseRef hiddenRef pv paletteRatio cut
        rF frF χ finest dimension' Kcap C),
      RP.graphMesh = Submission.Lib.K4DyadicRowScales.mesh nmesh → RP.Brow = 28 * Kg ^ 6 →
      (∀ a, Fp.active a → ∀ x ∈ RP.E1 (p.γ a) ∩ p.F a,
        |q / aA * Submission.Lib.K4GlobalParentSignal.rate (p.R a) x.1 x.2 -
          ∑ j : Fin 3, RP.row a (ancCode (d.N k) p a RP.graphMesh x) j *
            (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤
        80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24)) →
      (∀ a, Fp.active a → ∀ b w : ℝ, fineMeshA ≤ b → b ≤ 1 → fineMeshA ≤ w → w ≤ 1 →
        KcensusA ^ (100 : ℕ) * b ≤ 1 * w →
        (occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
        ((occupied (RP.E1 (p.γ a) ∩ p.F a) (fun z j => unshearedPacketBase p a z j)
          (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
          KcensusA / (b ^ 3 * w ^ dimension)) →
      ∃ (E1' : Fin (d.W k) → Set Ev) (hmeas : ∀ w, MeasurableSet (E1' w))
        (hsub : ∀ w, E1' w ⊆ RP.E1 w),
        (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w)) ≤
          (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E1' w)) + chargeN ∧
        SampleHbox hp (RP.restrict E1' hmeas hsub) radiusP stripWidth beta Mq Tq qmesh qerror
          qduration qbound Pfac chargeR η Lp ρ)
    -- the final mass
    (hRmass : ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w))
    (hreserve : ENNReal.ofReal (1 - gfraction)⁻¹ *
        (Pfac * (ENNReal.ofReal (2 / K) + 10000 * η) + chargeR + 6561 * beta + chargeN) +
      ((nfam : ENNReal) * (ENNReal.ofReal (4 * coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 28) *
          p.κ ^ 2) * (ENNReal.ofReal (θrow * (coreK p τ ^ FixedSourcePowers.coreRadius)⁻¹) +
            27 * (δref * ENNReal.ofReal (p.κ ^ 2)))) +
        (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal εMK +
          (ENNReal.ofReal ((KcensusA * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
            ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
              (7 : ℝ) ^ 4)) + 81 * betaR)) +
      ENNReal.ofReal cut * (⌈coreK p τ ^ 12⌉₊ : ENNReal) + ENNReal.ofReal (p.κ⁻¹ / 64) ≤
        ENNReal.ofReal (71 * p.κ⁻¹ / 512)) :
    ∃ (density : ℝ) (E : Fin (d.W k) → Set Ev), 0 < density ∧
      (∀ w, E w ⊆ Rp.residual w) ∧
      ENNReal.ofReal density + ENNReal.ofReal density ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w) ∧
      ∀ b : Fin p.C, p.lev b = i + c → Fp.active (p.par^[c] b) → d.ν k (p.γ b) (p.A b) ≠ 0 →
        ENNReal.ofReal density *
            (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) ≤
          ((d.ν k (p.γ b)).prod volume) (E (p.γ b) ∩ p.F b) →
        ∃ (Se Er bad : Set Ev) (st : Ev → ℕ) (G : ℕ → Fin 3 → ℝ) (pal : Measure (Fin 2 → ℤ)),
          Se ⊆ E (p.γ b) ∩ p.F b ∧ Se ⊆ Er ∧
          (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) /
              ENNReal.ofReal K ≤ (((d.ν k (p.γ b)).prod volume).restrict Se) Set.univ ∧
          CapClauses K ε d₁ (hRelOf (p.T i) (p.T (i + c))) (aRelOf (d.N k) (p.r i) (p.r (i + c)))
            (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
            (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
            (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
              O204.Split.δ (d.N k) (p.r (p.lev b))) Se ∧
          StateClauses K ε pvP (d.ν k (p.γ b))
            (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
            (fun z => O204.Tangent.packetSignal (p.R (p.par^[c] b)) z /
              O204.Split.δ (d.N k) (p.r (p.lev b))) Se st pal ∧
          RowClauses K θ aA q (p.R (p.par^[c] b))
            (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b)) Se Er st G ∧
          QualClauses Mq K θ aA q (p.j b) ((2 : ℝ) ^ p.T (p.lev b))⁻¹ (d.ν k (p.γ b))
            Se Er bad st G := by
  classical
  have hN1 : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hκ1 : 1 ≤ p.κ := hp.1
  obtain ⟨hK2304, hκK, hmax, hpower⟩ :=
    Submission.Lib.K4NativePreparationNumerics.native_pre_geometry_envelope_bounds
      (source := d.K k) hκ1 hN1 (by linarith : 0 ≤ τ + τ)
  obtain ⟨C, RP, hmeshRP, hBRP, hfitRaw, hoccRP, hmassP⟩ := sample_package
    hd hp hHE hH hτ Qp hpure Fp Rp nfam hdepth hr hrL hn jrec hjstop hwidthrec hbase hhidden
    hbaseSmall hcoreSmall hheightSmall pv paletteRatio hRatio hOriginal χ finest hχ hdim
    hprofileRec hbudget cut hcut c hqaA hmidfam hwidthfam hKc hwidthpos hwidthfloor hstrip hdeep
    hθrow hθrow1 hfraction δref hδ0 hδtop hβ1 hKK hgeometry hconstant w t hwidthPower hθPower
    hκ₁ nnA indexA hmatchA hsA dimension profileErrorA fineMeshA KcensusA gapPowerA hdim0 hdim1
    hprofileA hprofilePowerA hFineA hθKA hbudgetA hlastA hstepA nnB indexB hmatchB hsB hd₀ hd₁
    profileErrorB fineMeshB KcensusB gapPowerB hprofileB hprofilePowerB hFineB hθKB hbudgetB
    hlastB hstepB hTlb hscale hr0 hrLb hprof hε hres hKbase hKband hKc1 hKcK hfine hV0 hvel
    steps hFine1 hKcensus hsteps hresolved hcellRate hdurationRate hratio0 hbaseBudget
    hhiddenBudget betaR hbetaR hbetaRTop hwidthR hratio hri hrLi hprofile nmesh hmesh hcoarse
    hbandResolved hKgJ hKgRate hKgCount hbaseRho hcond hbaseRho4 hwRho hwRadius hgfraction
    hgfrac hεMK hsmall hθ80
  obtain ⟨E1', hmeas, hsub, hmassN, hboxN⟩ := hnative C RP hmeshRP hBRP hfitRaw hoccRP
  -- the final mass of the restricted package
  have hfinal : Pfac * (ENNReal.ofReal (2 / K) + 10000 * η) + chargeR + 6561 * beta ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) ((RP.restrict E1' hmeas hsub).E1 w) := by
    change _ ≤ ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E1' w)
    set X := Pfac * (ENNReal.ofReal (2 / K) + 10000 * η) + chargeR + 6561 * beta with hX
    set cfrac := ENNReal.ofReal (1 - gfraction)⁻¹ with hcfrac
    set rest := ((nfam : ENNReal) * (ENNReal.ofReal (4 * coreK p τ ^ (3 * FixedSourcePowers.coreRadius
        + 28) * p.κ ^ 2) * (ENNReal.ofReal (θrow * (coreK p τ ^ FixedSourcePowers.coreRadius)⁻¹) +
          27 * (δref * ENNReal.ofReal (p.κ ^ 2)))) +
        (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal εMK +
          (ENNReal.ofReal ((KcensusA * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
            ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
              (7 : ℝ) ^ 4)) + 81 * betaR)) +
      ENNReal.ofReal cut * (⌈coreK p τ ^ 12⌉₊ : ENNReal) + ENNReal.ofReal (p.κ⁻¹ / 64) with hrest
    have hgf1 : 0 < 1 - gfraction := by linarith
    have hc0 : cfrac ≠ 0 := by
      rw [hcfrac]; exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hgf1)).ne'
    have hctop : cfrac ≠ ⊤ := ENNReal.ofReal_ne_top
    have hrestTop : rest ≠ ⊤ := by
      have h1 : rest ≤ ENNReal.ofReal (71 * p.κ⁻¹ / 512) :=
        le_trans (le_add_self) (by rw [hrest]; simpa only [add_assoc] using hreserve)
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
    have hchain : cfrac * (X + chargeN) + rest ≤
        cfrac * ((∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E1' w)) + chargeN) +
          rest := by
      calc cfrac * (X + chargeN) + rest ≤ ENNReal.ofReal (71 * p.κ⁻¹ / 512) := by
            rw [hrest]; simpa only [add_assoc] using hreserve
        _ ≤ ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w) := hRmass
        _ ≤ cfrac * (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (RP.E1 w)) + rest := by
            rw [hrest]; simpa only [add_assoc] using hmassP
        _ ≤ _ := add_le_add (mul_le_mul' le_rfl hmassN) le_rfl
    have h2 := (ENNReal.add_le_add_iff_right hrestTop).mp hchain
    have h3 := (ENNReal.mul_le_mul_iff_right hc0 hctop).mp h2
    exact (ENNReal.add_le_add_iff_right hchargeN).mp h3
  have hgraphPos : 0 < (RP.restrict E1' hmeas hsub).graphMesh := by
    change 0 < RP.graphMesh
    rw [hmeshRP, ← hmesh]; positivity
  have hgraphBase' : 3 * baseRef ≤ (RP.restrict E1' hmeas hsub).graphMesh := by
    change _ ≤ RP.graphMesh
    rw [hmeshRP]; exact hgraphBase
  have hgraphHidden' : 3 * hiddenRef ≤ (RP.restrict E1' hmeas hsub).graphMesh := by
    change _ ≤ RP.graphMesh
    rw [hmeshRP]; exact hgraphHidden
  have hBK' : (RP.restrict E1' hmeas hsub).Brow ≤ K := by
    change RP.Brow ≤ K
    rw [hBRP]; exact hBK
  have hresE : ∀ w, Rp.residual w ⊆ d.E k w := fun w z hz => hHE w (Rp.subset_H w hz)
  have hresB : ∀ w, Rp.residual w ⊆ Qp.base w := fun w => broadResidual_subset_base Rp w
  exact samplePost_of_rootPackage Qp hpure hd hp hHE hH hibm hcstop hKpos hθpos hε haApos hqpos
    (RP.restrict E1' hmeas hsub) hbase hhidden hcut hfraction hgraphPos hfinePv hpvP hgraphBase'
    hgraphHidden' hphysicalBase hphysicalHidden beta hbeta hbetaTop hstripWidth hstripRatio
    hpaletteRatio hBK' radiusP stripWidth hNormalizedWidth hOriginalWidth Mq Tq qmesh qerror
    qduration qbound Pfac chargeR η hPfac hPfac0 hchargeR hη hLp hboxN hresE hresB hK2304 hmax
    hpower hκK (le_refl 5186) FixedSourcePowers.jet_bound jmid hmidb hmida hrmid hrLmid hwidthmid
    hsmallList hcount hqmesh hqbound hcoeff herror hduration hfinal

end Sample

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
