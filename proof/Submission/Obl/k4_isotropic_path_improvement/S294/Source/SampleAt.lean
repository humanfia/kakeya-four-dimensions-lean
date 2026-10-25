-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleAt, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- One sample of `StagesProducer` from its lanes (session x1088).

`sample_at` proves `StageAt … k σS` (one sample of `Source.StagesProducer`) by x1082's
`Source.SampleFinal.sample_final`, choosing and discharging:
* the core family: ALL levels `i, …, i + C - g` (`nfamAt`, `Source.SampleFamily`);
* every census side condition (`Source.CensusChoices`, one census constant `KcenAt`);
* the MK4 rows by `mk4_parameters` at the native fit target `θN = N^(-graphTargetCoeff gain L)`
  (x1096), `Vmax = 2 K_d`, `c = cE = κ⁻¹/512`, `ratio = 1/2·10^12`, mesh cap `1`
  (`Source.SampleChoices`); `θN ≤ θ` (`Source.SampleAtNumerics.thetaN_le_theta`);
* the child caps (`hres`, `hKbase`, `hKband`), `Kcensus ≤ K`, `Brow = 28 Kg^6 ≤ K`, `hcount`,
  the velocity bound, the levels and positivities, the band of the MK4 rows.
Premises: the pre-sample facts of `StagesProducer`, a handful of sample-level facts (each an
instance of an eventual lemma: `eventually_geom_le`, `eventually_brow_le`,
`eventually_hcount_native`, the list/band fits) and `LanesAt` — for every path at the sample,
the lanes `Source.LaneData` (records, native/qualification, the list budget at a middle depth,
the final reserve) at the choices of `Source.SampleChoices`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.StageAt
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.LaneData
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleChoices
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFinal
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFamily
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootCensusAt
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.BrowNumerics
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.CorePowers
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MK4TargetLower
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleScalars
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleNumerics
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleAtNumerics

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory Filter
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual
  likelihoodGood labelledSupport finitePacketHistory labelledVelocityPalette)
open scoped ENNReal

noncomputable section

/-- **The lanes of every path at one sample**, at the census/MK4 choices of `Source.SampleChoices`
(`Source.LaneData`). -/
def LanesAt (tune : Tuning) (d₁ κ₁ : ℝ) (Ep : ℕ) (precision loss e0 : ℝ) (m : ℕ) (s : ℕ → ℝ)
    (δ₀ : ℝ) (C : ℕ) (indices : Finset ℕ) (d : ProblemData) (Mp Dp : ℕ) (budget : ℝ) (k : ℕ)
    (σS : ℝ) : Prop :=
  ∀ (p : PathData (d.W k))
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σS)
    (H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (∀ w, MeasurableSet (H w)) →
    (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
    ENNReal.ofReal (p.κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
    ∀ (Qp : PreparedAngularPath d k p m H (fun _ : Fin 1 => d.η * d.L) (tauOf tune δ₀ d.L budget)),
    Qp.uniformPureBounds (tauOf tune δ₀ d.L budget) →
    ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Qp.residual w) →
    ∀ i ∈ indices,
    ∀ (Fp : PaletteFamily Qp i (i + C)
        (d.N k ^ (-paletteExpOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) d.L))
        (d.N k ^ entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L) /
          Submission.Lib.K4NativePreparationNumerics.palettePruningThreshold ⌈(4 * p.κ + 6) ^ 2⌉₊)
        (Submission.Lib.K4NativePreparationNumerics.lightParentThreshold p.κ))
      (Rp : BroadResidual Fp (d.N k ^ (-((ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) * d.L))) (2 * ((d.N k ^ budget) ^ 1)⁻¹)),
    ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w) →
    (∀ b, Fp.active b → Fp.U b ⊆
      likelihoodGood Qp.law (labelledSupport Qp.residual)
        (finitePacketHistory p.lev p.γ p.F)
        (labelledVelocityPalette
          (d.N k ^ (-ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L)))
        i (i + C)
        (d.N k ^ entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L))) →
    Nonempty (LaneData hp Qp Fp Rp (nfamAt κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m C) (childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)
      (KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L)
      (thetaOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L (p.r i) (p.r (i + (childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m))) (p.T i)
        (p.T (i + (childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m))))
      (epsOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L (p.r i) (p.r (i + (childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m))) (p.T i)
        (p.T (i + (childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m))))
      (O204.Split.δ (d.N k) (p.r i)) (((2 : ℝ) ^ p.T i)⁻¹) d₁ d₁
      (KcenAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m)
      (KgAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) d₁ m)
      (stepsAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m)
      (nmeshAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) d₁
        (thetaNAt κ₁ d₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L) m)
      (fineAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) d₁
        (thetaNAt κ₁ d₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L) m)
      (cellRateAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m) (durationRateAt p.κ (d.K k))
      (2 * d.K k) (1 / 4) (p.κ⁻¹ / 512) (θrowAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget))
      (1 / 2000000000000) (δrefAt (2 * ((d.N k ^ budget) ^ 1)⁻¹)) (qualDegree κ₁)
      (pvOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L (p.r i) (p.r (i + (childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m))) (p.T i)
        (p.T (i + (childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)))))

/-- **One sample of `StagesProducer`** from the lanes and the sample-level facts. -/
theorem sample_at (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    (hslackC : censusSlack ≤ tune.slack)
    {d₁ κ₁ ρ : ℝ} {Ep : ℕ} {precision loss e0 : ℝ}
    (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ < 1) (hκ₁ : 0 < κ₁) (hκ₁1 : κ₁ ≤ 1) (hρ : 0 < ρ) (hdρ : d₁ + ρ < 1)
    (hprec : 1 ≤ precision) (hloss : 0 < loss) (hloss1 : loss ≤ 1) (he0 : 0 < e0)
    {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {C target : ℕ} {indices : Finset ℕ}
    (hgrid : Parent.grid κ₁ ρ m s (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀
      (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) / 8))
    (hδtol : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0))
    (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁) (hm8 : 8 ≤ m)
    (hgm : 8 ≤ gridFineOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m)
    (htarget : target < m) (hstarget : s target = 1 / 2) (hm2 : 2 * (target + 1) = m)
    (hC1 : 1 ≤ C)
    (hCge : windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m ≤ C)
    (hCle : (C : ℝ) ≤
      windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m + 1)
    (hCt : C + 1 ≤ target) (hind : indices = Finset.range (target + 1 - C))
    {d : ProblemData} (hd : d.Valid)
    (hprof : ∀ r : ℝ, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L)
    {Mp Dp : ℕ} {budget : ℝ} (hbud : 0 < budget) (hbud1 : budget ≤ 1)
    {k : ℕ} {σS : ℝ} (hσS : 0 < σS)
    -- the eventual facts at this sample
    (hKd : d.K k ≤ d.N k ^ σS)
    (hgeomk : ∀ κ source τ : ℝ, 1 ≤ κ → κ ≤ d.N k ^ σS → source ≤ d.N k ^ σS → 0 ≤ τ →
      τ ≤ δ₀ * d.L →
      geomOf (Native.nativePreGeometryEnvelope κ source (d.N k) (2 * τ)) (d.N k) δ₀ d.L ≤
        d.N k ^ (3 * δ₀ * d.L))
    (hmN : (m : ℝ) ≤ d.N k ^ (2 * tauOf tune δ₀ d.L budget))
    (hσK : σS ≤ loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1) / 8)
    (h12 : (2 : ℝ) ^ 12 ≤
      d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1) / 8))
    (h2g : 2 ≤ d.N k ^ (gainOf tune κ₁ d₁ Ep precision loss e0 * d.L))
    (hbrowk : ∀ κ Kd Kc τ : ℝ, 1 ≤ κ → κ ≤ d.N k ^ σS → 1 ≤ Kd → Kd ≤ d.N k ^ σS → 1 ≤ Kc →
      Kc ≤ d.N k ^ ((3 * δ₀ *
        (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
        ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) +
        1 / (m : ℝ)) * d.L) → 0 ≤ τ → τ ≤ δ₀ * d.L →
      28 * mk4Kg κ (2 * Kd) Kc (64 * (max κ Kd) ^ 2 * κ * 4 ^ d₁ *
          d.N k ^ (2 * (δ₀ * d.L) + (τ + 2 * δ₀ * d.L) + τ)) (κ⁻¹ / 512)
          (d.N k ^ (-(ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) *
            d.L))) (δ₀ * d.L) (d.N k) ^ 6 ≤
        d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)))
    (hcountk : ∀ κ source tolerance : ℝ, 1 ≤ κ → κ ≤ d.N k ^ σS → source ≤ d.N k ^ σS →
      0 ≤ tolerance → tolerance ≤ 2 * tauOf tune δ₀ d.L budget →
      (Native.nativePreGeometryEnvelope κ source (d.N k) tolerance ^ 10 *
          (2 * Native.nativePreGeometryEnvelope κ source (d.N k) tolerance ^
            (3 * FixedSourcePowers.coreRadius + 18))) * 9 ^ 3 ≤
        d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)))
    -- the two census lists and the band fit in the family (the eventual layer)
    (hlistA : ∀ κ Kd : ℝ, 1 ≤ κ → κ ≤ d.N k ^ σS → 1 ≤ Kd → Kd ≤ d.N k ^ σS →
      listLenOf m δ₀ d.L (d.N k) (2 * (KgeomAt κ Kd (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget)) ^ (censusGp FixedSourcePowers.coreRadius
        FixedSourcePowers.jet (stripExpOf (KgeomAt κ Kd (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget)) κ (d.N k) δ₀ d.L (d.N k ^ (-((ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) * d.L))))
        (rowExpOf FixedSourcePowers.coreRadius) + 10) /
        fineAt κ Kd (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) d₁ (thetaNAt κ₁ d₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L) m) < nfamAt κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m C)
    (hlistB : ∀ κ Kd εv : ℝ, 1 ≤ κ → κ ≤ d.N k ^ σS → 1 ≤ Kd → Kd ≤ d.N k ^ σS →
      d.N k ^ (-(3 * (((Ep : ℝ) + 1) * precision + 3) * gainOf tune κ₁ d₁ Ep precision loss e0 *
        d.L / κ₁)) / 2 ≤ εv →
      childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m + listLenOf m δ₀ d.L (d.N k) (2 * (KgeomAt κ Kd (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget)) ^
        (censusGp FixedSourcePowers.coreRadius FixedSourcePowers.jet
          (stripExpOf (KgeomAt κ Kd (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget)) κ (d.N k) δ₀ d.L (d.N k ^ (-((ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) * d.L))))
          (rowExpOf FixedSourcePowers.coreRadius) + 10) / εv) < nfamAt κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m C)
    (hband : ∀ κ Kd : ℝ, 1 ≤ κ → κ ≤ d.N k ^ σS → 1 ≤ Kd → Kd ≤ d.N k ^ σS →
      d.N k ^ (-(d.L / 4)) ≤
        4 * Submission.Lib.K4DyadicRowScales.coarse (nmeshAt κ Kd (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) d₁ (thetaNAt κ₁ d₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L) m))
    -- the lanes
    (hlanes : LanesAt tune d₁ κ₁ Ep precision loss e0 m s δ₀ C indices d Mp Dp budget k σS) :
    StageAt tune d₁ κ₁ Ep precision loss e0 m s δ₀ C indices d Mp Dp budget k σS := by
  intro p hp H hHmeas hH hHmass Qp hpure hQmass i hi Fp Rp hRmass hgood
  classical
  -- the problem and the path
  have hN2 : 2 ≤ d.N k := hd.1 k
  have hN1 : 1 < d.N k := by linarith
  have hNp : 0 < d.N k := by linarith
  have hL : 0 < d.L := hd.2.2.2.1
  have hκ1 : 1 ≤ p.κ := hp.1
  have hκN : p.κ ≤ d.N k ^ σS := hp.2.1
  have hKd1 : 1 ≤ d.K k := hd.2.2.1.1 k
  have hpath := hp.2.2.2.2.1
  have hrb : ∀ l, l < m → |p.r l - s l * d.L| ≤ δ₀ * d.L := fun l hl => (hpath l hl).1
  have hTb : ∀ l, l < m → d.N k ^ ((κ₁ * s l - δ₀) * d.L) ≤ (2 : ℝ) ^ p.T l ∧
      (2 : ℝ) ^ p.T l ≤ d.N k ^ ((κ₁ * s l + δ₀) * d.L) :=
    fun l hl => ⟨(hpath l hl).2.2.1, (hpath l hl).2.2.2.1⟩
  have hm : 0 < m := by omega
  have hs : ∀ l, s l = ((l : ℝ) + 1) / m := hgrid.2.2.2.2.2.2.2.1
  have hδ₀ : 0 < δ₀ := hgrid.2.2.2.1
  have hgain : 0 < gainOf tune κ₁ d₁ Ep precision loss e0 := gainOf_pos hκ₁ hd₁1 hprec hloss he0
  have hδg : δ₀ ≤ gainOf tune κ₁ d₁ Ep precision loss e0 / 100 := hgrid.2.2.2.2.2.2.2.2.2.1
  have hmg : 1 / (m : ℝ) ≤ gainOf tune κ₁ d₁ Ep precision loss e0 / κ₁ :=
    hgrid.2.2.2.2.2.2.2.2.1
  have hiC : i + C ≤ target := by
    rw [hind, Finset.mem_range] at hi; omega
  have hiCm : i + C + 2 ≤ m := by omega
  have hδm1 : 4 * δ₀ * (m : ℝ) ≤ 1 := hδm.trans hκ₁1
  have hHE : ∀ w, H w ⊆ d.E k w := hp.residual_subset_event H hH
  have hτ0 : 0 ≤ tauOf tune δ₀ d.L budget := by
    unfold tauOf
    have := zero_le_one.trans tune.one_le_slack
    exact le_min (by positivity) (by positivity)
  have hτδ : tauOf tune δ₀ d.L budget ≤ δ₀ * d.L := min_le_left _ _
  -- the core constant and the census geometry
  have hKcore := hgeomk p.κ (d.K k) (tauOf tune δ₀ d.L budget) hκ1 hκN hKd hτ0 hτδ
  have e2τ : 2 * tauOf tune δ₀ d.L budget = tauOf tune δ₀ d.L budget + tauOf tune δ₀ d.L budget :=
    two_mul _
  rw [e2τ] at hKcore
  have hub0 : 0 ≤ ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) := by
    unfold ubOf
    have := tune.budget_pos κ₁ d₁ Ep precision loss
    positivity
  have hubL : 0 ≤ ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * d.L :=
    by positivity
  have hfr0 : 0 < 2 * ((d.N k ^ budget) ^ 1)⁻¹ := by positivity
  -- the core constant
  obtain ⟨hK2304, hκKc, hmaxKc, hpowKc⟩ :=
    Native.native_pre_geometry_envelope_bounds (source := d.K k) hκ1 hN1.le
      (by linarith : 0 ≤ tauOf tune δ₀ d.L budget + tauOf tune δ₀ d.L budget)
  have hκK' : p.κ ≤ coreK p (tauOf tune δ₀ d.L budget) := (le_max_left _ _).trans hmaxKc
  -- the census geometry
  obtain ⟨hKK, hNK, hconst⟩ := geomOf_ge (K := coreK p (tauOf tune δ₀ d.L budget)) (N := d.N k)
    (δ₀ := δ₀) (L := d.L)
  obtain ⟨Kgeom, hKgeom⟩ : ∃ x, x = geomOf (coreK p (tauOf tune δ₀ d.L budget)) (d.N k) δ₀ d.L :=
    ⟨_, rfl⟩
  rw [← hKgeom] at hKK hNK hconst
  have hKgeomN : Kgeom ≤ d.N k ^ (3 * δ₀ * d.L) := by rw [hKgeom]; exact hKcore
  have hKgeom1 : 1 < Kgeom := by linarith
  have hKgeom24 : 24 ≤ Kgeom := by linarith
  have hstrip := strip_spec hKgeom1 hκ1 hN1.le (by positivity : 0 ≤ 2 * δ₀ * d.L)
    (Real.rpow_pos_of_pos hNp
      (-(ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * d.L)))
    (Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by linarith)) (κ := p.κ)
  obtain ⟨w, hw⟩ : ∃ x, x = stripExpOf Kgeom p.κ (d.N k) δ₀ d.L
      (d.N k ^ (-(ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) *
        d.L))) := ⟨_, rfl⟩
  rw [← hw] at hstrip
  obtain ⟨gap, hgapdef⟩ : ∃ x, x = gapExpOf Kgeom (d.N k) δ₀ d.L m := ⟨_, rfl⟩
  have hgap : 2 * d.N k ^ ((1 / (m : ℝ) + 2 * δ₀) * d.L) ≤ Kgeom ^ gap := by
    rw [hgapdef]
    refine (logCeil_spec hKgeom1 ?_).1
    have : 1 ≤ d.N k ^ ((1 / (m : ℝ) + 2 * δ₀) * d.L) := Real.one_le_rpow hN1.le (by positivity)
    linarith
  obtain ⟨Kcen, hKcendef⟩ : ∃ x, x = censusKOf Kgeom FixedSourcePowers.coreRadius
      FixedSourcePowers.jet w (rowExpOf FixedSourcePowers.coreRadius) gap := ⟨_, rfl⟩
  have hKcen : 1 ≤ Kcen ∧ Kgeom ^ 3 ≤ Kcen := by
    rw [hKcendef]; exact censusK_ge hKgeom1.le _ _ _ _ _
  have hbudgetK : Kgeom ^ (3 * FixedSourcePowers.coreRadius + (((3 * FixedSourcePowers.coreRadius +
      58) + 8) * FixedSourcePowers.jet + w + rowExpOf FixedSourcePowers.coreRadius *
        ⌈coreRowC₀⌉₊ + 1) + gap + 83) ≤ Kcen := by
    rw [hKcendef]; unfold censusKOf censusGp; exact le_rfl
  -- the family
  obtain ⟨g, hg⟩ : ∃ x, x = familyMarginOf κ₁ δ₀
      (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m := ⟨_, rfl⟩
  have hgC : g ≤ C := by
    rw [hg]
    exact familyMargin_le_window tune hκ₁ hκ₁1 hd₁ hd₁1 hprec hloss hloss1 hgain hδ₀.le hm hslackC
      hδtol hδg hmg hCge
  obtain ⟨nfam, hnfam⟩ : ∃ x, x = C + 1 - g := ⟨_, rfl⟩
  -- the MK4 choices: fit target `θN`, `Vmax = 2 K_d`, rates `κ⁻¹/512`
  have hgt : 0 < NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision := by
    unfold NativeDesign.graphTargetCoeff
    have h1 := NativeDesign.floorEndCoeff_pos κ₁ d₁ (Ep := Ep) hprec
    have h2 := NativeDesign.clockCoeff_pos (Ep := Ep) hprec
    positivity
  obtain ⟨θN, hθN⟩ : ∃ x, x = d.N k ^ (-(NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision *
      gainOf tune κ₁ d₁ Ep precision loss e0 * d.L)) := ⟨_, rfl⟩
  have hθN0 : 0 < θN := by rw [hθN]; exact Real.rpow_pos_of_pos hNp _
  have hθN1 : θN ≤ 1 := by
    rw [hθN]
    apply Real.rpow_le_one_of_one_le_of_nonpos hN1.le
    have : 0 ≤ NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision *
      gainOf tune κ₁ d₁ Ep precision loss e0 * d.L := by positivity
    linarith
  have hκ0 : 0 < p.κ := by linarith
  have hcMK : 0 < p.κ⁻¹ / 512 := by positivity
  have hcMK1 : p.κ⁻¹ / 512 ≤ 1 := by
    have : p.κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ1
    linarith
  have hCband0 : 0 ≤ 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
      d.N k ^ (2 * (δ₀ * d.L) + (tauOf tune δ₀ d.L budget + 2 * δ₀ * d.L) +
        tauOf tune δ₀ d.L budget) := by
    have : 0 ≤ max p.κ (d.K k) := hκ0.le.trans (le_max_left _ _)
    positivity
  obtain ⟨hFine0, hFine1, -, hsteps, hresolved, hcellRate, hdurationRate, hmesh, hKgJ, hKgRate,
      hKgCount, hbaseRho, hcond, hbaseRho4, hwRho, hwRadius, hwidthR, hgf0, hgfrac, hεMK, hsmall,
      hθ80N, hrates, hmeshCap, hfineCap⟩ :=
    mk4_parameters (κ := p.κ) (Vmax := 2 * d.K k) (Kc := Kcen)
      (Cband := 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
        d.N k ^ (2 * (δ₀ * d.L) + (tauOf tune δ₀ d.L budget + 2 * δ₀ * d.L) +
          tauOf tune δ₀ d.L budget))
      (c := p.κ⁻¹ / 512) (cE := p.κ⁻¹ / 512) (ratio := 1 / 2000000000000) (θ := θN) (d := d₁)
      (N := d.N k) (δL := δ₀ * d.L)
      (frontRadius := d.N k ^ (-(ubOf tune κ₁ d₁ Ep precision loss
        (gainOf tune κ₁ d₁ Ep precision loss e0) * d.L))) (meshCap := 1)
      hκ1 (by linarith) hKcen.1 hCband0 hcMK hcMK1 hcMK hcMK1 (by norm_num) (by norm_num)
      hθN0 hθN1 hd₁ hd₁1 hN1.le (by positivity) (Real.rpow_pos_of_pos hNp _)
      (Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by linarith)) one_pos le_rfl
  obtain ⟨Kg, hKg⟩ : ∃ x, x = mk4Kg p.κ (2 * d.K k) Kcen (64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
      d.N k ^ (2 * (δ₀ * d.L) + (tauOf tune δ₀ d.L budget + 2 * δ₀ * d.L) +
        tauOf tune δ₀ d.L budget)) (p.κ⁻¹ / 512)
      (d.N k ^ (-(ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) *
        d.L))) (δ₀ * d.L) (d.N k) := ⟨_, rfl⟩
  rw [← hKg] at hFine0 hFine1 hresolved hmesh hKgJ hKgRate hKgCount hcond hsmall hθ80N hmeshCap hfineCap
  obtain ⟨steps, hstepsdef⟩ : ∃ x, x = stepsOf Kcen := ⟨_, rfl⟩
  rw [← hstepsdef] at hFine0 hFine1 hsteps hresolved hcellRate hmesh hrates hfineCap hKgCount
  obtain ⟨Tm, hTm⟩ : ∃ x, x = min (min (θN / (80 * Kg ^ 7)) 1) (min (1 / (64 * Kg))
      (min (1 / (36 * Kg ^ 4)) (((1 / 4 : ℝ) / 4) ^ 4 * (p.κ⁻¹ / 512) ^ 4 /
        (256 * Parent.ParentSource.Broad.Velocity.curvatureRowConstant ^ 3 * Kg ^ 9 + 1))))
      := ⟨_, rfl⟩
  rw [← hTm] at hFine0 hFine1 hresolved hmesh hsmall hθ80N hmeshCap hfineCap
  obtain ⟨nmesh, hnmesh⟩ : ∃ x, x = meshIndexOf Tm d₁ := ⟨_, rfl⟩
  rw [← hnmesh] at hFine0 hFine1 hresolved hmesh hsmall hθ80N hmeshCap hfineCap
  obtain ⟨fineMeshA, hfineA⟩ : ∃ x, x =
      Submission.Lib.K4DyadicRowScales.mesh nmesh / (2 : ℝ) ^ steps := ⟨_, rfl⟩
  rw [← hfineA] at hFine0 hFine1 hresolved hmesh hfineCap
  -- the child level and the lists
  obtain ⟨c, hc⟩ : ∃ x, x = childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m :=
    ⟨_, rfl⟩
  have hcC : c ≤ C := by
    rw [hc]
    refine childOffset_le_window hκ₁ hκ₁1 hd₁ hd₁1 hprec hgain hm ?_ hCge
    have := gridFineOf_le_gain tune hloss hloss1 hgain (κ₁ := κ₁) (d₁ := d₁) (Ep := Ep)
      (precision := precision)
    have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  obtain ⟨ε, hεdef⟩ : ∃ x, x = epsOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)
      (d.N k) d.L (p.r i) (p.r (i + c)) (p.T i) (p.T (i + c)) := ⟨_, rfl⟩
  obtain ⟨gp, hgp⟩ : ∃ x, x = censusGp FixedSourcePowers.coreRadius FixedSourcePowers.jet w
      (rowExpOf FixedSourcePowers.coreRadius) := ⟨_, rfl⟩
  obtain ⟨nnA, hnnAdef⟩ : ∃ x, x = listLenOf m δ₀ d.L (d.N k) (2 * Kgeom ^ (gp + 10) / fineMeshA) :=
    ⟨_, rfl⟩
  obtain ⟨nnB, hnnBdef⟩ : ∃ x, x = listLenOf m δ₀ d.L (d.N k) (2 * Kgeom ^ (gp + 10) / ε) :=
    ⟨_, rfl⟩
  have hεfloor : d.N k ^ (-(3 * (((Ep : ℝ) + 1) * precision + 3) *
      gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / κ₁)) / 2 ≤ ε := by
    rw [hεdef]
    have hsd : s (i + c) - s i = (c : ℝ) / m := by rw [hs, hs]; push_cast; ring
    have hsAB' : s (i + c) - s i ≤
        2 * (((Ep : ℝ) + 1) * precision + 3) * gainOf tune κ₁ d₁ Ep precision loss e0 / κ₁ := by
      rw [hsd, hc]; exact childOffset_div_le hκ₁ hm hgain hprec hmg
    have hX := eps_exponent_le (Ep := Ep) hL hgain hloss hloss1 hprec hκ₁ hκ₁1 (hrb i (by omega))
      (hrb (i + c) (by omega)) hsAB' hδg
    refine le_trans ?_ (epsOf_lower_power (N := d.N k) (L := d.L) (rA := p.r i) (rB := p.r (i + c))
      (precision := precision) (loss := loss) (gain := gainOf tune κ₁ d₁ Ep precision loss e0)
      Ep (p.T i) (p.T (i + c)) hNp)
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
  have hnnA : nnA < nfam := by
    have h := hlistA p.κ (d.K k) hκ1 hκN hKd1 hKd
    subst hnnAdef hnfam hg hgp hfineA hnmesh hTm hstepsdef hKg hθN hKcendef hw hgapdef hKgeom
    exact h
  have hnnB : c + nnB < nfam := by
    have h := hlistB p.κ (d.K k) ε hκ1 hκN hKd1 hKd hεfloor
    subst hnnBdef hnfam hg hgp hc hw hKgeom
    exact h
  -- the levels of the window
  have hlev_lt : ∀ l, l ≤ i + C → l < m := fun l hl => by omega
  have hrpos : ∀ l, l ≤ i + C → 0 ≤ p.r l := fun l hl => (hpath l (hlev_lt l hl)).2.1.le
  have hrL : ∀ l, l ≤ i + C → p.r l ≤ d.L := fun l hl =>
    r_le_L_of_grid hL hm hs hδm1 (by omega) (hrb l (hlev_lt l hl))
  have hfamC : ∀ j : Fin nfam, i + (j : ℕ) ≤ i + C := fun j => by have := j.isLt; omega
  have hmargin : 3 * δ₀ * (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
      ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) + 2 * δ₀ ≤
      κ₁ * (s (i + C) - s (i + nfam - 1)) := by
    apply familyMargin_spec hκ₁ hm hs (by positivity)
    rw [← hg]; omega
  have hδroot : 0 < O204.Split.δ (d.N k) (p.r i) := O204.Tangent.δ_pos _ _
  have hδlb : 0 < O204.Split.δ (d.N k) (p.r (i + c)) := O204.Tangent.δ_pos _ _
  have hG : 0 < Kgeom ^ (gp + 10) := by positivity
  -- the per-sample scalars
  have hkexp0 : 0 ≤ loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1) := by
    positivity
  have hpgl0 : 0 ≤ precision * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L := by
    have : (0 : ℝ) ≤ precision := by linarith
    positivity
  have hscal := sample_scalars_pos (Ep := Ep) (precision := precision) (loss := loss)
    (gain := gainOf tune κ₁ d₁ Ep precision loss e0) (L := d.L) (rA := p.r i) (rB := p.r (i + c))
    (TA := p.T i) (TB := p.T (i + c)) hN1 hkexp0 hpgl0
  have hεpos : 0 < ε := by rw [hεdef]; exact hscal.2.1
  have hic : i + c ≤ i + C := by omega
  have hTic : p.T i ≤ p.T (i + c) := path_T_le hp hN1 hL hm hs hδm hκ₁ (by omega) (by omega)
  have hsAB : s (i + c) - s i ≤
      2 * (((Ep : ℝ) + 1) * precision + 3) * gainOf tune κ₁ d₁ Ep precision loss e0 / κ₁ := by
    have hsd : s (i + c) - s i = (c : ℝ) / m := by rw [hs, hs]; push_cast; ring
    rw [hsd, hc]
    exact childOffset_div_le hκ₁ hm hgain hprec hmg
  -- the state mesh resolves the child's base and band
  have hfitε := eps_fit tune (Ep := Ep) hL hκ₁ hκ₁1 hd₁ hd₁1 hprec hloss hloss1 he0
    (hrb i (by omega)) (hrb (i + c) (by omega)) hsAB hδg hgrid.2.2.1
    (by rw [← hstarget]; exact s_le_of_le hm hs (by omega))
  have hres : d.N k ^ (-(d.L - p.r (i + c))) ≤ 4 * ε := by
    rw [hεdef]; exact eps_resolved hN1 hTic hpgl0 hkexp0 hfitε
  -- the cap constants below `K`
  have hκK8 : p.κ ≤ d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L /
      ((Ep : ℝ) + 1) / 8) := hκN.trans (Real.rpow_le_rpow_of_exponent_le hN1.le hσK)
  have hKd8 : d.K k ≤ d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L /
      ((Ep : ℝ) + 1) / 8) := hKd.trans (Real.rpow_le_rpow_of_exponent_le hN1.le hσK)
  have h6δ := six_delta_le tune (Ep := Ep) (κ₁ := κ₁) (d₁ := d₁) (precision := precision) hL hloss
    hgain hδ₀.le hδtol
  obtain ⟨hKbase, hKband⟩ := cap_constants_le_K hN1 (by positivity) hκ1 hκK8
    (by linarith) hKd8 hτ0 hτδ hτ0 hτδ (by positivity) h6δ h12 hd₁ hd₁1.le
  -- the census constant, the MK4 row constant and `K`
  have hKcenN : Kcen ≤ d.N k ^ ((3 * δ₀ *
      (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
      ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) + 1 / (m : ℝ)) *
        d.L) := by
    rw [hKcendef, hw, hgapdef]
    exact censusK_le_rpow hKgeom24 hκ1 (hκK'.trans hKK) hN1.le hNK (by positivity) hL.le hubL
      (by rw [show 3 * δ₀ * d.L = (3 * δ₀) * d.L by ring] at hKgeomN; exact hKgeomN)
  have hBK : 28 * Kg ^ 6 ≤ KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L := by
    have h := hbrowk p.κ (d.K k) Kcen (tauOf tune δ₀ d.L budget) hκ1 hκN hKd1 hKd hKcen.1 hKcenN
      hτ0 hτδ
    rw [← hKg] at h
    exact h
  have hKg1 : 1 ≤ Kg := by
    have : (1 : ℝ) ≤ 6 * (1 + 24 * p.κ + p.κ ^ 2 + 2 * d.K k) := by nlinarith
    linarith
  have hKcK : Kcen ≤ KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L := by
    have hc := Kc_le_mk4Kg (κ := p.κ) (Vmax := 2 * d.K k) (Kc := Kcen)
      (Cband := 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
        d.N k ^ (2 * (δ₀ * d.L) + (tauOf tune δ₀ d.L budget + 2 * δ₀ * d.L) +
          tauOf tune δ₀ d.L budget))
      (c := p.κ⁻¹ / 512) (frontRadius := d.N k ^ (-(ubOf tune κ₁ d₁ Ep precision loss
        (gainOf tune κ₁ d₁ Ep precision loss e0) * d.L))) (δL := δ₀ * d.L) (N := d.N k)
      hKcen.1 (one_le_cband hκ1 hd₁ hN1.le (by positivity)) hcMK hcMK1
    rw [← hKg] at hc
    exact le_K_of_brow hc hKg1 hBK
  -- the native fit target below `θ`
  have hgtc : 64 * (((Ep : ℝ) + 1) * precision + 3) / κ₁ ≤
      NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision := by
    unfold NativeDesign.graphTargetCoeff NativeDesign.clockCoeff
    have h1 := NativeDesign.floorEndCoeff_pos κ₁ d₁ (Ep := Ep) hprec
    have e : 16 * (4 * (((Ep : ℝ) + 1) * precision + 3)) / κ₁ =
        64 * (((Ep : ℝ) + 1) * precision + 3) / κ₁ := by ring
    rw [e]
    linarith
  have hθNθ : θN ≤ thetaOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L
      (p.r i) (p.r (i + c)) (p.T i) (p.T (i + c)) := by
    rw [hθN]
    exact thetaN_le_theta hN1 hL hgain hloss hloss1 hprec hκ₁ hκ₁1 (hrb i (by omega))
      (hrb (i + c) (by omega)) hsAB hδg hgtc h2g
  -- hcount, at the literal core envelope
  have hcount := hcountk p.κ (d.K k) (tauOf tune δ₀ d.L budget + tauOf tune δ₀ d.L budget) hκ1
    hκN hKd (by linarith) (by linarith)
  -- the family below the envelope
  have hn : (nfam : ℝ) ≤ coreK p (tauOf tune δ₀ d.L budget) := by
    have h1 : (nfam : ℝ) ≤ m := by exact_mod_cast (show nfam ≤ m by omega)
    have h2 : d.N k ^ (2 * tauOf tune δ₀ d.L budget) ≤ coreK p (tauOf tune δ₀ d.L budget) := by
      rw [two_mul]; exact hpowKc
    linarith
  have hlastA := census_list_last hN1 hL hm hG hFine0 hs hrb (a := i) (by rw [← hnnAdef]; omega)
  have hlastB := census_list_last hN1 hL hm hG hεpos hs hrb (a := i + c) (by rw [← hnnBdef]; omega)
  rw [← hnnAdef] at hlastA
  rw [← hnnBdef] at hlastB
  rw [hgp] at hlastA hlastB
  unfold censusGp at hlastA hlastB
  -- the band of the MK4 rows is resolved
  have hbandR : d.N k ^ (-(d.L - p.r i)) ≤
      4 * Submission.Lib.K4DyadicRowScales.coarse nmesh := by
    have h := hband p.κ (d.K k) hκ1 hκN hKd1 hKd
    have hri := (abs_le.mp (hrb i (by omega))).2
    have hsi : s i ≤ 1 / 2 := by rw [← hstarget]; exact s_le_of_le hm hs (by omega)
    have hδ14 : δ₀ ≤ 1 / 4 := by
      have : gainOf tune κ₁ d₁ Ep precision loss e0 ≤ 1 / 8 := hgrid.2.2.1
      linarith
    have hroom : d.L / 4 ≤ d.L - p.r i := by
      have h1 : s i * d.L ≤ 1 / 2 * d.L := mul_le_mul_of_nonneg_right hsi hL.le
      have h2 : δ₀ * d.L ≤ 1 / 4 * d.L := mul_le_mul_of_nonneg_right hδ14 hL.le
      linarith only [h1, h2, hri]
    have hle : d.N k ^ (-(d.L - p.r i)) ≤ d.N k ^ (-(d.L / 4)) :=
      Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith only [hroom])
    refine hle.trans ?_
    subst hnmesh hTm hKg hstepsdef hθN hKcendef hw hgapdef hKgeom
    exact h
  -- the lanes at this sample
  obtain ⟨L⟩ := hlanes p hp H hHmeas hH hHmass Qp hpure hQmass i hi Fp Rp hRmass hgood
  have e_Kcen : KcenAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m = Kcen := by
    rw [hKcendef, hw, hgapdef, hKgeom]; rfl
  have e_Kg : KgAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) d₁ m = Kg := by
    rw [hKg]; unfold KgAt; rw [e_Kcen]; rfl
  have e_steps : stepsAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m = steps := by
    rw [hstepsdef]; unfold stepsAt; rw [e_Kcen]
  have e_θN : thetaNAt κ₁ d₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L = θN := by rw [hθN]; rfl
  have e_nmesh : nmeshAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) d₁
      (thetaNAt κ₁ d₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L) m = nmesh := by
    rw [hnmesh, hTm]; unfold nmeshAt TmAt; rw [e_Kg, e_θN]
  have e_fine : fineAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) d₁
      (thetaNAt κ₁ d₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L) m = fineMeshA := by
    rw [hfineA]; unfold fineAt; rw [e_nmesh, e_steps]
  have e_cell : cellRateAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m =
      p.κ⁻¹ / 512 / (Kcen * ((2 : ℝ) ^ steps) ^ 3) := by
    unfold cellRateAt; rw [e_Kcen, e_steps]
  have e_nfam : nfamAt κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m C = nfam := by rw [hnfam, hg]; rfl
  have e_ε : epsOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L (p.r i)
      (p.r (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)) (p.T i)
      (p.T (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)) = ε := by rw [hεdef, hc]
  have e_θrow : θrowAt p.κ (d.K k) (d.N k) δ₀ d.L (tauOf tune δ₀ d.L budget) =
      (Kgeom ^ rowExpOf FixedSourcePowers.coreRadius)⁻¹ := by rw [hKgeom]; rfl
  rw [e_fine, e_nmesh, e_cell, e_Kg, e_steps, e_Kcen, e_nfam, e_ε, ← hc, e_θrow] at L
  obtain ⟨density, E, hdens, hEres, hEmass, hchild⟩ := sample_final
    (K := KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L)
    (θ := thetaOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L (p.r i)
      (p.r (i + c)) (p.T i) (p.T (i + c)))
    (ε := ε) (aA := O204.Split.δ (d.N k) (p.r i)) (q := ((2 : ℝ) ^ p.T i)⁻¹) (d₁ := d₁)
    (Kc := Kgeom ^ (3 * FixedSourcePowers.coreRadius + 66)) (width := (Kgeom ^ w)⁻¹)
    (θrow := (Kgeom ^ rowExpOf FixedSourcePowers.coreRadius)⁻¹)
    (qc := layerQOf w FixedSourcePowers.coreRadius) (Kgeom := Kgeom) (Vmax := 2 * d.K k)
    (f₀' := d.f 0) (perror := δ₀ * d.L) (gfraction := 1 / 4) (εMK := p.κ⁻¹ / 512) (Kg := Kg)
    (chargeN := L.chargeN) (ρ := L.ρ) (Lp := L.Lp) (pvP := L.pvP) (baseRef := L.baseRef)
    (hiddenRef := L.hiddenRef) (dimension' := L.dimension') (f₀ := L.f₀)
    (profileError := L.profileError) (Kcap := L.Kcap)
    hd hp hHE hH hτ0 Qp hpure Fp Rp
    nfam (fun j => hlev_lt _ (hfamC j)) (fun j => hrpos _ (hfamC j)) (fun j => hrL _ (hfamC j))
    hn
    -- records (x1095)
    L.jrec L.hjstop L.hwidthrec L.hbase L.hhidden L.hbaseSmall L.hcoreSmall L.hheightSmall
    L.pv L.paletteRatio L.hRatio L.hOriginal L.χ L.finest L.hχ L.hdim L.hprofileRec L.hbudget
    L.cut L.hcut
    -- the per-sample scalars
    c rfl
    -- the census
    (fun j => by have := hfamC j; omega)
    (fun j => path_delta_le hp hN1.le hL hm hs hδm hκ₁1 (Nat.le_add_right _ _)
      (hlev_lt _ (hfamC j)))
    (layer_const (by linarith) hKK (by linarith) FixedSourcePowers.coreRadius) (by positivity)
    (layer_floor hKgeom1.le w FixedSourcePowers.coreRadius) hstrip.2.2
    (fun j fine deep hfine hdeep' => by
      unfold PathData.deepBaseRadius
      rw [hfine, hdeep']
      exact family_deep hN1 hL hm hs hδm hκ₁ hTb hκ1 hκK' hKK hNK hKgeom24 hKgeomN hδ₀.le hub0
        hstrip.2.1 (by omega) hiCm j.isLt hmargin)
    (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hKgeom1.le)) hfr0.le
    (ENNReal.ofReal (16 * (2 * ((d.N k ^ budget) ^ 1)⁻¹)))
    (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
    ENNReal.ofReal_ne_top
    (by
      rw [← ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_div_of_pos (by linarith)]
      have e : 8 * (2 * ((d.N k ^ budget) ^ 1)⁻¹) / (16 * (2 * ((d.N k ^ budget) ^ 1)⁻¹)) =
          1 / 2 := by field_simp; ring
      rw [e]
      simp)
    hKK hNK hconst w (rowExpOf FixedSourcePowers.coreRadius) le_rfl le_rfl hκ₁1
    -- the root's MK4 census
    nnA (fun j => ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩) (fun j => rfl)
    (fun j => s_le_of_le hm hs (by omega))
    d₁ (2 * δ₀ * d.L) fineMeshA Kcen gap hd₁ hd₁1
    (fun j => profile_pair hprof (hrpos _ (by have := j.isLt; omega))
      (hrL _ (by have := j.isLt; omega)) (hrpos _ (by have := j.isLt; omega))
      (hrL _ (by have := j.isLt; omega)))
    hNK hFine0
    (by
      have hδ0 : Parent.ParentSource.δ (d.N k) (p.r i) ≠ 0 := (O204.Tangent.δ_pos _ _).ne'
      have h2T : (2 : ℝ) ^ p.T i ≠ 0 := by positivity
      rw [div_self hδ0, div_self h2T, div_one]
      exact hKcen.1)
    hbudgetK hlastA
    (fun j hj => census_step hN1 hm hs hrb hgap hδroot (by omega))
    -- the children's census
    nnB (fun j => ⟨c + (j : ℕ) + 1, by have := j.isLt; omega⟩) (fun j => rfl)
    (fun j => s_le_of_le hm hs (by omega))
    hd₁ hd₁1 (2 * δ₀ * d.L) ε Kcen gap
    (fun j => profile_pair hprof (hrpos _ (by omega)) (hrL _ (by omega))
      (hrpos _ (by have := j.isLt; omega)) (hrL _ (by have := j.isLt; omega)))
    hNK hεpos
    (census_shape hN1 hL.le hκ₁1 (hrb i (by omega)) (hrb (i + c) (by omega))
      (s_le_of_le hm hs (by omega)) (hTb i (by omega)).1 (hTb (i + c) (by omega)).2 hNK
      (by linarith) hKcen.2)
    hbudgetK hlastB
    (fun j hj => census_step hN1 hm hs hrb hgap hδlb (by omega))
    (path_T_le hp hN1 hL hm hs hδm hκ₁ (by omega) (by omega))
    (path_delta_le hp hN1.le hL hm hs hδm hκ₁1 (by omega) (by omega))
    (hrpos _ (by omega)) (hrL _ (by omega)) hprof hεpos hres hKbase hKband hKcen.1 hKcK le_rfl
    -- the velocity bound and the MK4 rows
    (by linarith) (residual_velocity_le Qp Rp)
    steps hFine1 hKcen.1 hsteps hresolved hcellRate hdurationRate (by norm_num) L.hbaseBudget
    L.hhiddenBudget L.betaR L.hbetaR L.hbetaRTop hwidthR L.hratio (hrpos _ (by omega))
    (hrL _ (by omega)) hprof
    nmesh hmesh rfl hbandR hKgJ hKgRate hKgCount hbaseRho hcond hbaseRho4 hwRho
    (by rw [show 2 * δ₀ * d.L = 2 * (δ₀ * d.L) by ring]; exact hwRadius)
    (by norm_num) hgfrac hεMK hsmall (hθ80N.trans hθNθ)
    -- records/states (x1095)
    L.hfinePv L.hpvP L.hgraphBase L.hgraphHidden L.hphysicalBase L.hphysicalHidden L.beta L.hbeta
    L.hbetaTop L.hstripWidth L.hstripRatio L.hpaletteRatio hBK L.radiusP L.stripWidth
    L.hNormalizedWidth L.hOriginalWidth
    -- qualification (x1096)
    L.Mq L.Tq L.qmesh L.qerror L.qduration L.qbound L.Pfac L.chargeR L.η L.hPfac L.hPfac0
    L.hchargeR L.hη L.hLp
    -- the lists
    L.jmid L.hmidb L.hmida L.hrmid L.hrLmid L.hwidthmid L.hsmallList hcount
    -- qualification numerics
    L.hqmesh L.hqbound L.hcoeff L.herror L.hduration
    -- levels and positivity
    (by omega) hic (Real.rpow_pos_of_pos hNp _) hscal.1 hδroot (by positivity)
    -- native (x1096), mass
    L.hchargeN L.hnative hRmass L.hreserve
  refine ⟨density, E, hdens, hEres, hEmass, ?_⟩
  intro b hb hact hν hmb
  subst hεdef hc
  have h := hchild b hb hact hν hmb
  rw [L.Mq_eq, L.pvP_eq] at h
  simp only [hb] at h ⊢
  exact h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
