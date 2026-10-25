-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleKeyAt, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.StageGlue
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.GridMono
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleScalars

/-!
# One sample of `StageAt` from the blocks (session x1082)

`sampleKey_at`: `Source.SampleFinal.sample_final` at a literal sample of `StageAt` (the path `p`, the
prepared path `Qp`, the palette family `Fp` of the window `i .. i + C`, the broad residual `Rp`),
with every hypothesis that only depends on the sample discharged here (`H ⊆ E`, the tolerance
`τ = tauOf`, the levels `i + c ≤ i + C < m`, the order and positivity of the clocks, depths and
scalars) and the literal scalars `c = childOffset`, `K = KOf`, `θ = thetaOf`, `ε = epsOf`,
`pv = pvOf`, `aA = δ(N, r_i)`, `q = 2^-T_i`, `M = qualDegree κ₁` fixed by defining equations (pass
`rfl`). The remaining inputs are exactly the blocks of `sample_final` (census, records, MK4,
states, native scales, lists, mass), with their names and types in `Source/SampleFinal.lean`.
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

set_option maxHeartbeats 4000000 in
/-- **One sample of `StageAt`**: `SampleKey` from the blocks of `sample_final`. -/
theorem sampleKey_at (tune : Tuning) {d₁ κ₁ : ℝ} {Ep : ℕ} {precision loss e0 : ℝ} {m : ℕ}
    {s : ℕ → ℝ} {δ₀ : ℝ} {C : ℕ}
    -- the outer scalars
    (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1) (hκpos : 0 < κ₁) (hprec : 1 ≤ precision) (hloss : 0 < loss)
    (he0 : 0 < e0) (hs : ∀ l, s l = ((l : ℝ) + 1) / m) (hδpos : 0 < δ₀)
    (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁) (hm : 0 < m)
    (hC : windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m ≤ C)
    (hgm : 8 ≤ (gainOf tune κ₁ d₁ Ep precision loss e0) * (m : ℝ))
    {d : ProblemData} (hd : d.Valid)
    (hprof : ∀ r : ℝ, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L)
    {Mp Dp : ℕ} {budget : ℝ} (hbud : 0 < budget) {k : ℕ} {σS : ℝ}
    -- the sample
    {p : PathData (d.W k)}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σS)
    {H : Fin (d.W k) → Set Ev}
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {τ : ℝ} (hτdef : τ = tauOf tune δ₀ d.L budget)
    (Qp : PreparedAngularPath d k p m H (fun _ : Fin 1 => d.η * d.L) τ)
    (hpure : Qp.uniformPureBounds τ)
    {i stop : ℕ} (hib : i + C < m) (hstopdef : stop = i + C)
    {meshF envF : ℝ} {θF : ENNReal} (Fp : PaletteFamily Qp i stop meshF envF θF)
    {rF frF : ℝ} (Rp : BroadResidual Fp rF frF)
    (hRmass : ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w))
    {pv paletteRatio : ℝ} (hRatio : 0 ≤ paletteRatio)
    (hOriginal : ∀ b, Fp.active b → Fp.U b ⊆ likelihoodGood Qp.law (labelledSupport Qp.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette pv) i stop paletteRatio)
    {c : ℕ} (hcdef : c = childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)
    {K θ ε aA q pvP : ℝ}
    (hKdef : K = KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L)
    (hθdef : θ = thetaOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L (p.r i) (p.r (i + c)) (p.T i)
      (p.T (i + c)))
    (hεdef : ε = epsOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L (p.r i) (p.r (i + c)) (p.T i)
      (p.T (i + c)))
    (hpvPdef : pvP = pvOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L (p.r i) (p.r (i + c)) (p.T i)
      (p.T (i + c)))
    (haAdef : aA = O204.Split.δ (d.N k) (p.r i)) (hqdef : q = ((2 : ℝ) ^ p.T i)⁻¹)
    {Mq : ℕ} (hMqdef : Mq = qualDegree κ₁)
    -- the blocks of `sample_final`
    (nfam : ℕ)
    (hdepth : ∀ j : Fin nfam, i + (j : ℕ) < m)
    (hr : ∀ j : Fin nfam, 0 ≤ p.r (i + (j : ℕ)))
    (hrL : ∀ j : Fin nfam, p.r (i + (j : ℕ)) ≤ d.L)
    (hn : (nfam : ℝ) ≤ Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ))
    (jrec : Fin nfam)
    (hjstop : i + (jrec : ℕ) ≤ stop)
    (hwidthrec : δ (d.N k) (p.r (i + (jrec : ℕ))) ≤ δ (d.N k) (p.r i))
    {baseRef hiddenRef : ℝ}
    (hbase : 0 < baseRef)
    (hhidden : 0 < hiddenRef)
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
    (χ finest : ℝ)
    (hχ : 0 ≤ χ)
    {dimension' f₀ profileError Kcap : ℝ}
    (hdim : 0 ≤ dimension')
    (hprofileRec : ∀ x, 0 ≤ x → x ≤ d.L → |d.f x - f₀ - dimension' * x| ≤ profileError)
    (hbudget : 512 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension' *
      d.N k ^ (2 * profileError + (τ + 2 * δ₀ * d.L) + τ) ≤ Kcap)
    (cut : ℝ)
    (hcut : 0 < cut)
    (hmidfam : ∀ j : Fin nfam, i + (j : ℕ) ≤ stop)
    (hwidthfam : ∀ j : Fin nfam,
      Parent.ParentSource.δ (d.N k) (p.r (i + (j : ℕ))) ≤ Parent.ParentSource.δ (d.N k) (p.r i))
    {Kc width θrow : ℝ}
    {qc : ℕ}
    (hKc : 2 * coreK p τ ^ ((3 * FixedSourcePowers.coreRadius + 58) + 7) ≤ Kc)
    (hwidthpos : 0 < width)
    (hwidthfloor : (Kc ^ qc)⁻¹ ≤ width)
    (hstrip : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ rF)
    (hdeep : ∀ j : Fin nfam, ∀ fine deep : Fin p.C, p.lev fine = i + (j : ℕ) → p.lev deep = stop →
      6 * coreK p τ ^ FixedSourcePowers.coreRadius * p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤
        renewalCellMesh Kc FixedSourcePowers.jet qc)
    (hθrow : 0 < θrow)
    (hθrow1 : θrow ≤ 1)
    (hfraction : 0 ≤ frF)
    (δref : ENNReal)
    (hδ0 : δref ≠ 0)
    (hδtop : δref ≠ ∞)
    (hβ1 : δref⁻¹ * ENNReal.ofReal (8 * frF) < 1)
    {Kgeom : ℝ}
    (hKK : coreK p τ ≤ Kgeom)
    (hgeometry : d.N k ^ (2 * δ₀ * d.L) ≤ Kgeom)
    (hconstant : 96 * coreRowK₀ ≤ Kgeom)
    (w t : ℕ)
    (hwidthPower : (Kgeom ^ w)⁻¹ ≤ width)
    (hθPower : (Kgeom ^ t)⁻¹ ≤ θrow)
    (hκ₁ : κ₁ ≤ 1)
    (nnA : ℕ)
    (indexA : Fin nnA → Fin nfam)
    (hmatchA : ∀ j, (indexA j : ℕ) = j.val + 1)
    (hsA : ∀ j : Fin nnA, s i ≤ s (i + (j.val + 1)))
    (dimension profileErrorA fineMeshA KcensusA : ℝ)
    (gapPowerA : ℕ)
    (hdim0 : 0 ≤ dimension)
    (hdim1 : dimension < 1)
    (hprofileA : ∀ j : Fin nnA, d.f (p.r (i + (j.val + 1))) - d.f (p.r i) ≤
      dimension * (p.r (i + (j.val + 1)) - p.r i) + profileErrorA)
    (hprofilePowerA : d.N k ^ profileErrorA ≤ Kgeom)
    (hFineA : 0 < fineMeshA)
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
    (nnB : ℕ)
    (indexB : Fin nnB → Fin nfam)
    (hmatchB : ∀ j, (indexB j : ℕ) = c + j.val + 1)
    (hsB : ∀ j : Fin nnB, s (i + c) ≤ s (i + c + (j.val + 1)))
    (profileErrorB fineMeshB KcensusB : ℝ)
    (gapPowerB : ℕ)
    (hprofileB : ∀ j : Fin nnB, d.f (p.r (i + c + (j.val + 1))) - d.f (p.r (i + c)) ≤
      d₁ * (p.r (i + c + (j.val + 1)) - p.r (i + c)) + profileErrorB)
    (hprofilePowerB : d.N k ^ profileErrorB ≤ Kgeom)
    (hFineB : 0 < fineMeshB)
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
    (hres : d.N k ^ (-(d.L - p.r (i + c))) ≤ 4 * ε)
    (hKbase : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * d.N k ^ (τ + 2 * δ₀ * d.L + τ) ≤ K)
    (hKband : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
      d.N k ^ (2 * (δ₀ * d.L) + (τ + 2 * δ₀ * d.L) + τ) ≤ K)
    (hKc1 : 1 ≤ KcensusB)
    (hKcK : KcensusB ≤ K)
    (hfine : fineMeshB ≤ ε)
    {Vmax : ℝ}
    (hV0 : 0 ≤ Vmax)
    (hvel : ∀ w, ∀ z ∈ Rp.residual w, ‖Parent.v z.1‖ ≤ Vmax)
    {cellRate durationRate coarse radius ratio : ℝ}
    (steps : ℕ)
    (hFine1 : fineMeshA ≤ 1)
    (hKcensus : 1 ≤ KcensusA)
    (hsteps : KcensusA ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps)
    (hresolved : fineMeshA * (2 : ℝ) ^ steps ≤ 1)
    (hcellRate : 0 < cellRate)
    (hdurationRate : 0 < durationRate)
    (hratio0 : 0 ≤ ratio)
    (hbaseBudget : 3 * baseRef ≤ fineMeshA * (2 : ℝ) ^ steps)
    (hhiddenBudget : 3 * hiddenRef ≤ fineMeshA * (2 : ℝ) ^ steps)
    (betaR : ENNReal)
    (hbetaR : betaR ≠ 0)
    (hbetaRTop : betaR ≠ ⊤)
    (hwidthR : (6 * p.κ) * radius ≤ rF)
    (hratio : ENNReal.ofReal ((8 * frF) / cut) / betaR ≤ ENNReal.ofReal ratio)
    {f₀' perror : ℝ}
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - f₀' - dimension * r| ≤ perror)
    (nmesh : ℕ)
    (hmesh : fineMeshA * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh nmesh)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse nmesh)
    (hbandResolved : d.N k ^ (-(d.L - p.r i)) ≤ 4 * coarse)
    {Kg baseRho wMK gfraction εMK : ℝ}
    (hKgJ : 6 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) ≤ Kg)
    (hKgRate : durationRate⁻¹ ≤ Kg)
    (hKgCount : 8 * (64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
      d.N k ^ (2 * perror + (τ + 2 * δ₀ * d.L) + τ)) / cellRate ≤ Kg)
    (hbaseRho : 0 ≤ baseRho)
    (hcond : 1 ≤ Kg * baseRho ^ 3)
    (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (Vmax + 1) * baseRho ≤ wMK)
    (hwRadius : wMK * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (hgfraction : 0 < gfraction)
    (hgfrac : gfraction < 1 - ratio)
    (hεMK : 0 < εMK)
    (hsmall : Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24) ≤
      min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
        ((gfraction / 4) ^ 4 * εMK ^ 4 /
          (256 * Parent.ParentSource.Broad.Velocity.curvatureRowConstant ^ 3 * Kg ^ 9 + 1))))
    (hθ80 : 80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh nmesh ^ ((1 - dimension) / 24) ≤
      θ)
    (hfinePv : 0 < pv)
    (hpvP : pv ≤ pvP)
    (hgraphBase : 3 * baseRef ≤ Submission.Lib.K4DyadicRowScales.mesh nmesh)
    (hgraphHidden : 3 * hiddenRef ≤ Submission.Lib.K4DyadicRowScales.mesh nmesh)
    (hphysicalBase : ∀ b, p.lev b = i + c →
      3 * ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev (p.par^[c] b))) * baseRef ≤ ε)
    (hphysicalHidden : ∀ b, p.lev b = i + c →
      3 * (δ (d.N k) (p.r (p.lev (p.par^[c] b))) / δ (d.N k) (p.r (p.lev b))) * hiddenRef ≤
        (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev b))) * ε)
    (beta : ENNReal)
    (hbeta : beta ≠ 0)
    (hbetaTop : beta ≠ ⊤)
    (hstripWidth : ∀ b, p.lev b = i + c →
      (K / 4) ^ (-100 : ℝ) * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (p.par^[c] b) j l|) ≤
        rF * ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)) * |(p.Q (p.par^[c] b)).det|))
    (hstripRatio : ENNReal.ofReal ((8 * frF) / cut) / beta ≤ (1 / 2000000000000 : ENNReal))
    (hpaletteRatio : ENNReal.ofReal ((8 * paletteRatio) / cut) / beta ≤ ENNReal.ofReal (K / 4))
    (hBK : 28 * Kg ^ 6 ≤ K)
    (radiusP stripWidth : ℝ)
    (hNormalizedWidth : (6 * p.κ) * radiusP ≤ rF)
    (hOriginalWidth : ∀ b, p.lev b = i + c →
      stripWidth * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (p.par^[c] b) j l|) ≤
        rF * ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)) * |(p.Q (p.par^[c] b)).det|))
    (Tq : ℕ)
    (qmesh qerror qduration : ℝ)
    (qbound : ℤ)
    (Pfac chargeR η : ENNReal)
    (hPfac : Pfac ≠ ⊤)
    (hPfac0 : Pfac ≠ 0)
    (hchargeR : chargeR ≠ ⊤)
    (hη : η ≠ ⊤)
    {Lp ρ : ℝ}
    (hLp : 0 ≤ Lp)
    (jmid : Fin nfam)
    (hmidb : ∀ b, p.lev b = i + c → (i + (jmid : ℕ)) ≤ p.lev b)
    (hmida : ∀ b, p.lev b = i + c → p.lev b - c ≤ (i + (jmid : ℕ)))
    (hrmid : 0 ≤ p.r ((i + (jmid : ℕ))))
    (hrLmid : p.r ((i + (jmid : ℕ))) ≤ d.L)
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
    (hqmesh : 0 ≤ qmesh)
    (hqbound : 0 ≤ qbound)
    (hcoeff : Parent.QualificationClock.coefficientCost Mq * (qmesh * qbound) ≤ K)
    (herror : qerror ≤ θ)
    (hduration : ∀ b, p.lev b = i + c → 1 / K ≤ qduration / ((((2 : ℝ) ^ p.T (p.lev b))⁻¹) /
      (((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)))⁻¹)))
    {chargeN : ENNReal}
    (hchargeN : chargeN ≠ ⊤)
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
    SampleKey tune d₁ κ₁ Ep precision loss e0 m d k p i Rp := by
  subst hτdef hstopdef hcdef hKdef hθdef hεdef hpvPdef haAdef hqdef hMqdef
  have hN2 : (2 : ℝ) ≤ d.N k := hd.1 k
  have hN1 : (1 : ℝ) < d.N k := by linarith
  have hL : 0 < d.L := hd.2.2.2.1
  have hgain : 0 < gainOf tune κ₁ d₁ Ep precision loss e0 := gainOf_pos (tune := tune) (Ep := Ep) hκpos hd₁ hprec hloss he0
  have hcC : childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m ≤ C :=
    childOffset_le_window hκpos hκ₁ hd₀ hd₁ hprec hgain hm hgm hC
  have hibm : i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m ≤ m - 1 := by omega
  have hcstop : i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m ≤ i + C := by omega
  have hicm : i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m < m := by omega
  have him : i < m := by omega
  -- the sample's own facts
  have hHE : ∀ w, H w ⊆ d.E k w := by
    intro w z hz
    obtain ⟨b, -, hγ, hzF⟩ := hH w hz
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -⟩ := hch
    rw [← hγ]
    exact (hF z hzF).1
  have hτ : 0 ≤ tauOf tune δ₀ d.L budget := by
    have hsl := tune.one_le_slack
    unfold tauOf
    exact le_min (by positivity) (by positivity)
  have hqaA : ((2 : ℝ) ^ p.T i)⁻¹ / O204.Split.δ (d.N k) (p.r i) =
      ((2 : ℝ) ^ p.T i)⁻¹ / Parent.ParentSource.δ (d.N k) (p.r i) := rfl
  have hTlb : p.T i ≤ p.T (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m) :=
    path_T_le hp hN1 hL hm hs hδm hκpos (Nat.le_add_right _ _) hicm
  have hscale : O204.Split.δ (d.N k) (p.r (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)) ≤
      O204.Split.δ (d.N k) (p.r i) :=
    path_delta_le hp hN1.le hL hm hs hδm hκ₁ (Nat.le_add_right _ _) hicm
  have hrpos : ∀ l, l < m → 0 < p.r l := fun l hl => (hp.2.2.2.2.1 l hl).2.1
  have hrLe : ∀ l, l < m → p.r l ≤ d.L := by
    intro l hl
    have h := path_r_le hp hL hm hs hδm hκ₁ (show l ≤ m - 1 by omega) (by omega)
    rw [hp.2.2.2.1] at h
    exact h
  have hr0 := (hrpos _ hicm).le
  have hrLb := hrLe _ hicm
  have hri := (hrpos _ him).le
  have hrLi := hrLe _ him
  obtain ⟨hθpos, hε, -, -, -⟩ := sample_scalars_pos (Ep := Ep) (precision := precision)
    (loss := loss) (gain := gainOf tune κ₁ d₁ Ep precision loss e0) (N := d.N k) (L := d.L) (rA := p.r i)
    (rB := p.r (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)) (TA := p.T i)
    (TB := p.T (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)) hN1 (by positivity) (by positivity)
  have hKpos : 0 < KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L := Real.rpow_pos_of_pos (by linarith) _
  have haApos : 0 < O204.Split.δ (d.N k) (p.r i) := O204.Tangent.δ_pos _ _
  have hqpos : (0 : ℝ) < ((2 : ℝ) ^ p.T i)⁻¹ := by positivity
  exact sample_final (hd := hd) (hp := hp) (hHE := hHE) (hH := hH) (hτ := hτ) (Qp := Qp) (hpure := hpure) (Fp := Fp) (Rp := Rp) (nfam := nfam) (hdepth := hdepth) (hr := hr) (hrL := hrL) (hn := hn) (jrec := jrec) (hjstop := hjstop) (hwidthrec := hwidthrec) (hbase := hbase) (hhidden := hhidden) (hbaseSmall := hbaseSmall) (hcoreSmall := hcoreSmall) (hheightSmall := hheightSmall) (pv := _) (paletteRatio := _) (hRatio := hRatio) (hOriginal := hOriginal) (χ := χ) (finest := finest) (hχ := hχ) (hdim := hdim) (hprofileRec := hprofileRec) (hbudget := hbudget) (cut := cut) (hcut := hcut) (c := _) (hqaA := hqaA) (hmidfam := hmidfam) (hwidthfam := hwidthfam) (hKc := hKc) (hwidthpos := hwidthpos) (hwidthfloor := hwidthfloor) (hstrip := hstrip) (hdeep := hdeep) (hθrow := hθrow) (hθrow1 := hθrow1) (hfraction := hfraction) (δref := δref) (hδ0 := hδ0) (hδtop := hδtop) (hβ1 := hβ1) (hKK := hKK) (hgeometry := hgeometry) (hconstant := hconstant) (w := w) (t := t) (hwidthPower := hwidthPower) (hθPower := hθPower) (hκ₁ := hκ₁) (nnA := nnA) (indexA := indexA) (hmatchA := hmatchA) (hsA := hsA) (dimension := dimension) (profileErrorA := profileErrorA) (fineMeshA := fineMeshA) (KcensusA := KcensusA) (gapPowerA := gapPowerA) (hdim0 := hdim0) (hdim1 := hdim1) (hprofileA := hprofileA) (hprofilePowerA := hprofilePowerA) (hFineA := hFineA) (hθKA := hθKA) (hbudgetA := hbudgetA) (hlastA := hlastA) (hstepA := hstepA) (nnB := nnB) (indexB := indexB) (hmatchB := hmatchB) (hsB := hsB) (hd₀ := hd₀) (hd₁ := hd₁) (profileErrorB := profileErrorB) (fineMeshB := fineMeshB) (KcensusB := KcensusB) (gapPowerB := gapPowerB) (hprofileB := hprofileB) (hprofilePowerB := hprofilePowerB) (hFineB := hFineB) (hθKB := hθKB) (hbudgetB := hbudgetB) (hlastB := hlastB) (hstepB := hstepB) (hTlb := hTlb) (hscale := hscale) (hr0 := hr0) (hrLb := hrLb) (hprof := hprof) (hε := hε) (hres := hres) (hKbase := hKbase) (hKband := hKband) (hKc1 := hKc1) (hKcK := hKcK) (hfine := hfine) (hV0 := hV0) (hvel := hvel) (steps := steps) (hFine1 := hFine1) (hKcensus := hKcensus) (hsteps := hsteps) (hresolved := hresolved) (hcellRate := hcellRate) (hdurationRate := hdurationRate) (hratio0 := hratio0) (hbaseBudget := hbaseBudget) (hhiddenBudget := hhiddenBudget) (betaR := betaR) (hbetaR := hbetaR) (hbetaRTop := hbetaRTop) (hwidthR := hwidthR) (hratio := hratio) (hri := hri) (hrLi := hrLi) (hprofile := hprofile) (nmesh := nmesh) (hmesh := hmesh) (hcoarse := hcoarse) (hbandResolved := hbandResolved) (hKgJ := hKgJ) (hKgRate := hKgRate) (hKgCount := hKgCount) (hbaseRho := hbaseRho) (hcond := hcond) (hbaseRho4 := hbaseRho4) (hwRho := hwRho) (hwRadius := hwRadius) (hgfraction := hgfraction) (hgfrac := hgfrac) (hεMK := hεMK) (hsmall := hsmall) (hθ80 := hθ80) (hfinePv := hfinePv) (hpvP := hpvP) (hgraphBase := hgraphBase) (hgraphHidden := hgraphHidden) (hphysicalBase := hphysicalBase) (hphysicalHidden := hphysicalHidden) (beta := beta) (hbeta := hbeta) (hbetaTop := hbetaTop) (hstripWidth := hstripWidth) (hstripRatio := hstripRatio) (hpaletteRatio := hpaletteRatio) (hBK := hBK) (radiusP := radiusP) (stripWidth := stripWidth) (hNormalizedWidth := hNormalizedWidth) (hOriginalWidth := hOriginalWidth) (Mq := _) (Tq := Tq) (qmesh := qmesh) (qerror := qerror) (qduration := qduration) (qbound := qbound) (Pfac := Pfac) (chargeR := chargeR) (η := η) (hPfac := hPfac) (hPfac0 := hPfac0) (hchargeR := hchargeR) (hη := hη) (hLp := hLp) (jmid := jmid) (hmidb := hmidb) (hmida := hmida) (hrmid := hrmid) (hrLmid := hrLmid) (hwidthmid := hwidthmid) (hsmallList := hsmallList) (hcount := hcount) (hqmesh := hqmesh) (hqbound := hqbound) (hcoeff := hcoeff) (herror := herror) (hduration := hduration) (hibm := hibm) (hcstop := hcstop) (hKpos := hKpos) (hθpos := hθpos) (haApos := haApos) (hqpos := hqpos) (hchargeN := hchargeN) (hnative := hnative) (hRmass := hRmass) (hreserve := hreserve)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
