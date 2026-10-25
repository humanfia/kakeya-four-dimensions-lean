-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeScaleAtSample, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleAtPath
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleDataMono
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeCensusPowerBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeOriginalSourceBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleChoices

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set Filter MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)
open Parent.Qualification.Jets2
open Submission.Lib.K4ContinuousKakeya

noncomputable section

/-- The literal MK4 mesh choices have native accuracy. -/
theorem sample_native_mk4_fit
    {kappa source N delta L tau ub dimension target : ℝ} {m : ℕ}
    (hKappa : 1 ≤ kappa) (hSource : 0 ≤ source) (hN : 1 ≤ N)
    (hDelta : 0 ≤ delta*L) (hUb : 0 ≤ ub*L)
    (hDimension : 0 ≤ dimension) (hDimension1 : dimension < 1)
    (hTarget : 0 < target) (hTarget1 : target ≤ 1)
    (hCensus : 1 ≤ KcenAt kappa source N delta L tau ub m) :
    1 ≤ KgAt kappa source N delta L tau ub dimension m ∧
      80*KgAt kappa source N delta L tau ub dimension m^7*
        Submission.Lib.K4DyadicRowScales.mesh
          (nmeshAt kappa source N delta L tau ub dimension target m)^((1-dimension)/24) ≤ target := by
  have hKappa0 : 0 < kappa := zero_lt_one.trans_le hKappa
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hc : 0 < kappa⁻¹/512 := by positivity
  have hc1 : kappa⁻¹/512 ≤ 1 := by
    have hh := inv_le_one_of_one_le₀ hKappa
    linarith only [hh]
  have hCband : 0 ≤ CbandAt kappa source N delta L tau dimension := by
    unfold CbandAt
    positivity
  obtain ⟨_,_,_,_,_,_,_,_,hKg,_,_,_,_,_,_,_,_,_,_,_,_,hFit,_,_,_⟩ :=
    mk4_parameters (κ:=kappa) (Vmax:=2*source) (Kc:=KcenAt kappa source N delta L tau ub m)
      (Cband:=CbandAt kappa source N delta L tau dimension)
      (c:=kappa⁻¹/512) (cE:=kappa⁻¹/512) (ratio:=1/2000000000000)
      (θ:=target) (d:=dimension) (N:=N) (δL:=delta*L) (frontRadius:=N^(-(ub*L))) (meshCap:=1)
      hKappa (by positivity) hCensus hCband hc hc1 hc hc1 (by norm_num) (by norm_num)
      hTarget hTarget1 hDimension hDimension1 hN hDelta (Real.rpow_pos_of_pos hN0 _)
      (Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith only [hUb])) one_pos le_rfl
  refine ⟨?_,hFit⟩
  apply le_trans _ hKg
  have hSquare : 0 ≤ kappa^2 := sq_nonneg _
  nlinarith only [hKappa0,hSource,hSquare]

/-- Uniform native scale data at the exact census, MK4 mesh and
strip choices of `SampleChoices`. All numeric choices are constructed;
the common tail precedes every path, sample and front budget. -/
theorem eventually_native_sample_scale_data
    (tune : Tuning) (hSlack : censusSlack ≤ tune.slack)
    (d : ProblemData) (hd : d.Valid) (design : NativeScaleDesign)
    {gain delta : ℝ} {m : ℕ} {s : ℕ → ℝ}
    (hGain : design.gainL=gain*d.L) (hGainPos : 0 < gain)
    (hDelta : 0 < delta) (hDeltaGain : delta ≤ gain/100)
    (hBudget : tune.budget design.kappa1 design.dimension design.Ep design.precision design.loss=
      NativeDesign.budget design.kappa1 design.dimension design.Ep design.precision design.loss)
    (hTolerance : delta ≤ tolOf tune design.kappa1 design.dimension design.Ep design.precision design.loss gain)
    (hGrid : 8 ≤ gridFineOf tune design.kappa1 design.dimension design.Ep design.precision design.loss gain*(m:ℝ))
    (hs : ∀ l, s l=((l:ℝ)+1)/m)
    (Cmk : ℝ) (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 3 Cmk) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ (sigmaPath : ℝ), sigmaPath ≤ sigma →
      ∀ (p : PathData (d.W k)) (Mp Dp : ℕ),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
        design.kappa1 m s delta Mp Dp sigmaPath →
      ∀ front : ℝ, 0 < front → ∀ i : ℕ,
      i+childOffset design.kappa1 design.Ep design.precision gain m < m →
      let tau := tauOf tune delta d.L front
      let ub := ubOf tune design.kappa1 design.dimension design.Ep design.precision design.loss gain
      let target := thetaNAt design.kappa1 design.dimension design.Ep design.precision gain (d.N k) d.L
      Nonempty (NativeScaleData design (d.N k) sigmaPath
        (p.T (i+childOffset design.kappa1 design.Ep design.precision gain m)-p.T i)
        (3*nmeshAt p.κ (d.K k) (d.N k) delta d.L tau ub design.dimension target m)
        (stepsAt p.κ (d.K k) (d.N k) delta d.L tau ub m)
        (KcenAt p.κ (d.K k) (d.N k) delta d.L tau ub m)
        ((d.N k)^(-design.coefficient))
        (thetaOf design.Ep design.precision design.loss gain (d.N k) d.L (p.r i)
          (p.r (i+childOffset design.kappa1 design.Ep design.precision gain m)) (p.T i)
          (p.T (i+childOffset design.kappa1 design.Ep design.precision gain m)))) := by
  have hN := hd.tendsto
  have hL : 0 < d.L := hd.2.2.2.1
  have v := native_scale_design_bounds design
  have hDelta0 := hDelta.le
  have hGridGain := gridFineOf_le_gain (κ₁:=design.kappa1) (d₁:=design.dimension) (Ep:=design.Ep) (precision:=design.precision)
    tune design.valid.2.2.2.2.2.1
    design.valid.2.2.2.2.2.2 hGainPos
  have hgm : 8 ≤ gain*(m:ℝ) := hGrid.trans
    (mul_le_mul_of_nonneg_right hGridGain (Nat.cast_nonneg _))
  obtain ⟨hCoefficient,_,hDeltaPower⟩ := native_design_original_source_exponents tune design.valid
    hBudget hGainPos hL hDelta0 hTolerance (divisor:=1) (by norm_num)
  have hDeltaPower' : 4*delta*d.L ≤ design.coefficient/2 := by
    change delta*d.L ≤ (NativeDesign.coefficientCoeff design.kappa1 design.dimension design.Ep
      design.precision design.loss*(gain*d.L))/10000000 at hDeltaPower
    rw [←hGain] at hDeltaPower hCoefficient
    change 0 < design.coefficient at hCoefficient
    change delta*d.L ≤ design.coefficient/10000000 at hDeltaPower
    linarith only [hDeltaPower,hCoefficient]
  obtain ⟨sigmaNative,hSigmaNative,hSigmaNative1,hNative⟩ := eventually_native_scale_data_at_path
    d.N hN design hL hGainPos hGain hDelta0 hDeltaGain hDeltaPower' hgm hs Cmk hCmk hMK
  obtain ⟨sigmaGeom,hSigmaGeom,hSigmaGeom1,hGeom⟩ := eventually_geom_le d.N hN hDelta hL
  let sigma := min sigmaNative sigmaGeom
  have hSigma : 0 < sigma := lt_min hSigmaNative hSigmaGeom
  have hSigmaNativeLe : sigma ≤ sigmaNative := min_le_left _ _
  have hSigmaGeomLe : sigma ≤ sigmaGeom := min_le_right _ _
  have hSource := hd.2.2.1.2 sigma hSigma
  have hLarge := ((tendsto_rpow_atTop
    (by linarith only [v.coefficient_pos] : 0 < design.coefficient/1000000)).comp hN).eventually_ge_atTop 20000
  refine ⟨sigma,hSigma,hSigmaNativeLe.trans hSigmaNative1,?_⟩
  filter_upwards [hNative,hGeom,hSource,hLarge] with k hNative hGeom hSource hLarge
  intro sigmaPath hSigmaPath p Mp Dp hp front hFront i hib tau ub target
  have hNk : (1:ℝ) < d.N k := lt_of_lt_of_le (by norm_num) (hd.1 k)
  have hNk0 : 0 < d.N k := zero_lt_one.trans hNk
  have hTau0 : 0 ≤ tau := by
    dsimp only [tau,tauOf]
    have hSlackPos := zero_lt_one.trans_le tune.one_le_slack
    positivity
  have hTau : tau ≤ delta*d.L := min_le_left _ _
  have hUb0 : 0 ≤ ub := by
    dsimp only [ub,ubOf]
    have hBudgetPos := tune.budget_pos design.kappa1 design.dimension design.Ep design.precision design.loss
    have hKappa1Pos := design.valid.2.2.1
    have hLossPos := design.valid.2.2.2.2.2.1
    positivity
  have hKappaGeom : p.κ ≤ d.N k^sigmaGeom := hp.2.1.trans
    (Real.rpow_le_rpow_of_exponent_le hNk.le (hSigmaPath.trans hSigmaGeomLe))
  have hSourceGeom : d.K k ≤ d.N k^sigmaGeom := hSource.trans
    (Real.rpow_le_rpow_of_exponent_le hNk.le hSigmaGeomLe)
  have hGeometry : KgeomAt p.κ (d.K k) (d.N k) delta d.L tau ≤ d.N k^(3*delta*d.L) := by
    simpa only [KgeomAt,two_mul] using
      (hGeom p.κ (d.K k) tau hp.1 hKappaGeom hSourceGeom hTau0 hTau)
  obtain ⟨hCore2304,_,hMax,_⟩ := Native.native_pre_geometry_envelope_bounds
    (source:=d.K k) hp.1 hNk.le (add_nonneg hTau0 hTau0)
  have hCoreGeom : Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (tau+tau) ≤ KgeomAt p.κ (d.K k) (d.N k) delta d.L tau := geomOf_ge.1
  have hKGeom : 24 ≤ KgeomAt p.κ (d.K k) (d.N k) delta d.L tau :=
    (by norm_num : (24:ℝ) ≤ 2304).trans (hCore2304.trans hCoreGeom)
  have hKappaG : p.κ ≤ KgeomAt p.κ (d.K k) (d.N k) delta d.L tau :=
    ((le_max_left _ _).trans hMax).trans hCoreGeom
  have hNKGeom : d.N k^(2*delta*d.L) ≤ KgeomAt p.κ (d.K k) (d.N k) delta d.L tau := by
    simpa only [KgeomAt] using (geomOf_ge (K:=Native.nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (tau+tau)) (N:=d.N k) (δ₀:=delta) (L:=d.L)).2.1
  have hCensus : 1 ≤ KcenAt p.κ (d.K k) (d.N k) delta d.L tau ub m :=
    (censusK_ge (by linarith only [hKGeom] : 1 ≤ KgeomAt p.κ (d.K k) (d.N k) delta d.L tau) _ _ _ _ _).1
  have hCensusPower : KcenAt p.κ (d.K k) (d.N k) delta d.L tau ub m ≤
      d.N k^(design.coefficient/1000) := by
    have hPower := native_sample_census_power_bound tune design.valid hBudget hGainPos hL hDelta0 hSlack
      hTolerance hGrid hNk.le hKGeom hp.1 hKappaG hNKGeom
      (by simpa only [mul_assoc] using hGeometry)
    simpa only [KcenAt,NativeScaleDesign.coefficient,hGain,ub] using hPower
  obtain ⟨_,hStepsUpper⟩ := native_census_steps_power_budget hNk.le v.coefficient_pos hLarge hCensus hCensusPower
  have hTargetEq : target=d.N k^(-design.target) := by
    dsimp only [target,thetaNAt,NativeScaleDesign.target]
    rw [hGain]
    congr 1
    ring
  have hTarget0 : 0 < target := by rw [hTargetEq]; positivity
  have hTarget1 : target ≤ 1 := by
    rw [hTargetEq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNk.le (neg_nonpos.mpr v.target_pos.le)
  obtain ⟨hKg,hFit⟩ := sample_native_mk4_fit hp.1 (zero_le_one.trans (hd.2.2.1.1 k)) hNk.le
    (mul_nonneg hDelta0 hL.le) (mul_nonneg hUb0 hL.le) design.valid.1 design.valid.2.1
    hTarget0 hTarget1 hCensus
  obtain ⟨native⟩ := hNative (d.W k) p (d.ω k) (d.ν k) (d.E k) (d.B k) d.f Mp Dp sigmaPath hp i hib
    (nmeshAt p.κ (d.K k) (d.N k) delta d.L tau ub design.dimension target m)
    (stepsAt p.κ (d.K k) (d.N k) delta d.L tau ub m)
    (KcenAt p.κ (d.K k) (d.N k) delta d.L tau ub m) (d.N k^(-design.coefficient))
    (KgAt p.κ (d.K k) (d.N k) delta d.L tau ub design.dimension m) hKg
    (by simpa only [hTargetEq] using hFit) hCensus hCensusPower
    (two_pow_stepsOf hCensus).1 hStepsUpper le_rfl
  exact ⟨native.restrict_sigma hNk.le (hSigmaPath.trans hSigmaNativeLe)⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
