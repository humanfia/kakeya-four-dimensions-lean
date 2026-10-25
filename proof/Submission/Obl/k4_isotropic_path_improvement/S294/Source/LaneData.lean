-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.LaneData, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The lanes of a sample (session x1088).

`LaneData` packs, at one sample of the front, every parameter and hypothesis of x1082's
`Source.SampleFinal.sample_final` that is NOT chosen by the census/MK4 lane of `Source.SampleAt`:
the record lane (x1095), the native/qualification lane (x1096, `native_root_step`), the list budget
at a middle depth and the final mass reserve. Its fields are `sample_final`'s binders verbatim; its
parameters are the sample objects and the census/MK4 choices they refer to
(`Source.SampleChoices`). Two further fields pin the qualification degree and the state palette
mesh to the values of `StagesProducer` (`Mq = qualDegree κ₁`, `pvP = pvOf …`). -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFinal

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual
  likelihoodGood labelledSupport finitePacketHistory labelledVelocityPalette)
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal

noncomputable section

/-- **The lanes of one sample.** -/
structure LaneData {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {H : Fin (d.W k) → Set Ev} {τ : ℝ}
    (Qp : PreparedAngularPath d k p m H (fun _ : Fin 1 => d.η * d.L) τ)
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} (Fp : PaletteFamily Qp i stop meshF envF θF)
    {rF frF : ℝ} (Rp : BroadResidual Fp rF frF)
    (nfam c : ℕ) (K θ ε aA q d₁ dimension KcensusA Kg : ℝ) (steps nmesh : ℕ)
    (fineMeshA cellRate durationRate Vmax gfraction εMK θrow ratio : ℝ) (δref : ENNReal)
    (MqGoal : ℕ) (pvGoal : ℝ) where
  jrec : Fin nfam
  hjstop : i + (jrec : ℕ) ≤ stop
  hwidthrec : δ (d.N k) (p.r (i + (jrec : ℕ))) ≤ δ (d.N k) (p.r i)
  baseRef : ℝ
  hiddenRef : ℝ
  hbase : 0 < baseRef
  hhidden : 0 < hiddenRef
  hbaseSmall : ∀ root : Fin p.C, p.lev root = i → ∀ deep : Fin p.C, p.lev deep = stop →
      p.unshearedDeepRadius root deep ≤ baseRef
  hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine = i + (jrec : ℕ) → p.lev deep = stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤
      (Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + τ) ^
      FixedSourcePowers.coreRadius)⁻¹ / 12
  hheightSmall : ∀ root : Fin p.C, p.lev root = i →
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
      hiddenRef
  pv : ℝ
  paletteRatio : ℝ
  hRatio : 0 ≤ paletteRatio
  hOriginal : ∀ b, Fp.active b → Fp.U b ⊆ likelihoodGood Qp.law (labelledSupport Qp.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette pv) i stop paletteRatio
  χ : ℝ
  finest : ℝ
  hχ : 0 ≤ χ
  dimension' : ℝ
  f₀ : ℝ
  profileError : ℝ
  Kcap : ℝ
  hdim : 0 ≤ dimension'
  hprofileRec : ∀ x, 0 ≤ x → x ≤ d.L → |d.f x - f₀ - dimension' * x| ≤ profileError
  hbudget : 512 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension' *
      d.N k ^ (2 * profileError + (τ + 2 * δ₀ * d.L) + τ) ≤ Kcap
  cut : ℝ
  hcut : 0 < cut
  hbaseBudget : 3 * baseRef ≤ fineMeshA * (2 : ℝ) ^ steps
  hhiddenBudget : 3 * hiddenRef ≤ fineMeshA * (2 : ℝ) ^ steps
  betaR : ENNReal
  hbetaR : betaR ≠ 0
  hbetaRTop : betaR ≠ ⊤
  hratio : ENNReal.ofReal ((8 * frF) / cut) / betaR ≤ ENNReal.ofReal ratio
  hfinePv : 0 < pv
  pvP : ℝ
  hpvP : pv ≤ pvP
  hgraphBase : 3 * baseRef ≤ Submission.Lib.K4DyadicRowScales.mesh nmesh
  hgraphHidden : 3 * hiddenRef ≤ Submission.Lib.K4DyadicRowScales.mesh nmesh
  hphysicalBase : ∀ b, p.lev b = i + c →
      3 * ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev (p.par^[c] b))) * baseRef ≤ ε
  hphysicalHidden : ∀ b, p.lev b = i + c →
      3 * (δ (d.N k) (p.r (p.lev (p.par^[c] b))) / δ (d.N k) (p.r (p.lev b))) * hiddenRef ≤
      (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev b))) * ε
  beta : ENNReal
  hbeta : beta ≠ 0
  hbetaTop : beta ≠ ⊤
  hstripWidth : ∀ b, p.lev b = i + c →
      (K / 4) ^ (-100 : ℝ) * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (p.par^[c] b) j l|) ≤
      rF * ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)) * |(p.Q (p.par^[c] b)).det|)
  hstripRatio : ENNReal.ofReal ((8 * frF) / cut) / beta ≤ (1 / 2000000000000 : ENNReal)
  hpaletteRatio : ENNReal.ofReal ((8 * paletteRatio) / cut) / beta ≤ ENNReal.ofReal (K / 4)
  radiusP : ℝ
  stripWidth : ℝ
  hNormalizedWidth : (6 * p.κ) * radiusP ≤ rF
  hOriginalWidth : ∀ b, p.lev b = i + c →
      stripWidth * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (p.par^[c] b) j l|) ≤
      rF * ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)) * |(p.Q (p.par^[c] b)).det|)
  Mq : ℕ
  Tq : ℕ
  qmesh : ℝ
  qerror : ℝ
  qduration : ℝ
  qbound : ℤ
  Pfac : ENNReal
  chargeR : ENNReal
  η : ENNReal
  hPfac : Pfac ≠ ⊤
  hPfac0 : Pfac ≠ 0
  hchargeR : chargeR ≠ ⊤
  hη : η ≠ ⊤
  Lp : ℝ
  ρ : ℝ
  hLp : 0 ≤ Lp
  jmid : Fin nfam
  hmidb : ∀ b, p.lev b = i + c → (i + (jmid : ℕ)) ≤ p.lev b
  hmida : ∀ b, p.lev b = i + c → p.lev b - c ≤ (i + (jmid : ℕ))
  hrmid : 0 ≤ p.r ((i + (jmid : ℕ)))
  hrLmid : p.r ((i + (jmid : ℕ))) ≤ d.L
  hwidthmid : δ (d.N k) (p.r ((i + (jmid : ℕ)))) ≤ δ (d.N k) (p.r i)
  hsmallList : ∀ b, p.lev b = i + c →
      ((aA / q) * Lp) * ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
      ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)))⁻¹) * (2 * θ) +
      (2 * (coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹ * (δ (d.N k) (p.r ((i + (jmid : ℕ)))) /
      δ (d.N k) (p.r (p.lev (p.par^[c] b))))) +
      ((coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 58 + 7)) ^ FixedSourcePowers.jet * (p.κ + coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹)) *
      (coreK p τ ^ FixedSourcePowers.coreRadius * ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
      ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
      ((2 : ℝ) ^ p.T (p.lev (p.par^[p.lev b - (i + (jmid : ℕ))] b)))⁻¹) * (6 * θ))))) +
      ρ) ≤ (aA / q) * θ
  hqmesh : 0 ≤ qmesh
  hqbound : 0 ≤ qbound
  hcoeff : Parent.QualificationClock.coefficientCost Mq * (qmesh * qbound) ≤ K
  herror : qerror ≤ θ
  hduration : ∀ b, p.lev b = i + c → 1 / K ≤ qduration / ((((2 : ℝ) ^ p.T (p.lev b))⁻¹) /
      (((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)))⁻¹))
  chargeN : ENNReal
  hchargeN : chargeN ≠ ⊤
  hnative : ∀ (C : BroadMultiscaleCoreSource d k p Rp.residual nfam (fun j => i + (j : ℕ))
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
      qduration qbound Pfac chargeR η Lp ρ
  hreserve : ENNReal.ofReal (1 - gfraction)⁻¹ *
      (Pfac * (ENNReal.ofReal (2 / K) + 10000 * η) + chargeR + 6561 * beta + chargeN) +
      ((nfam : ENNReal) * (ENNReal.ofReal (4 * coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 28) *
      p.κ ^ 2) * (ENNReal.ofReal (θrow * (coreK p τ ^ FixedSourcePowers.coreRadius)⁻¹) +
      27 * (δref * ENNReal.ofReal (p.κ ^ 2)))) +
      (ENNReal.ofReal (1 - gfraction)⁻¹ * ENNReal.ofReal εMK +
      (ENNReal.ofReal ((KcensusA * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
      ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
      (7 : ℝ) ^ 4)) + 81 * betaR)) +
      ENNReal.ofReal cut * (⌈coreK p τ ^ 12⌉₊ : ENNReal) + ENNReal.ofReal (p.κ⁻¹ / 64) ≤
      ENNReal.ofReal (71 * p.κ⁻¹ / 512)
  Mq_eq : Mq = MqGoal
  pvP_eq : pvP = pvGoal

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
