-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeScaleFactory, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleDesignIdentities
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeQualificationPowerBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativePreStatePrimitiveBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativePreStateMassBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeSupportScalarBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeSupportMassBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeFailureTail
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesignBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootScaleAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeNumeratorPowerBudget

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set Filter MeasureTheory
open Parent.Qualification
open Parent.Qualification.Jets2
open Parent.Qualification.PhysicalModel
open Submission.Lib.K4ContinuousKakeya
open scoped ENNReal

noncomputable section

/-- Uniform actual native scalar choices. The common tail precedes
the child clock, original graph mesh, census scales, strip width and
final display scale. No source, row or analytic certificate is an input. -/
theorem eventually_native_scale_data
    (N : ℕ→ℝ) (hN : Tendsto N atTop atTop) (q : NativeScaleDesign)
    (Cmk : ℝ) (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 3 Cmk) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ (T fine steps : ℕ) (Kcensus stripWidth theta : ℝ),
      0 < T →
      q.gainL ≤ nativeClockExponent (N k) T →
      nativeClockExponent (N k) T ≤ NativeDesign.clockCoeff q.Ep q.precision*q.gainL →
      dyadicParameterWidth fine ≤ (N k)^(-q.target) →
      1 ≤ Kcensus → Kcensus ≤ (N k)^(q.coefficient/1000) →
      Kcensus^(100:ℕ) ≤ (2:ℝ)^steps → (2:ℝ)^steps ≤ (N k)^(q.coefficient/5) →
      (N k)^(-q.coefficient) ≤ stripWidth →
      (N k)^(-q.thetaFloor) ≤ theta → theta ≤ (N k)^q.coefficient →
      (((2:ℝ)^T)⁻¹)^((q.degree:ℝ)+1/8) ≤ (N k)^(-2*q.thetaFloor) →
      Nonempty (NativeScaleData q (N k) sigma T fine steps Kcensus stripWidth theta) := by
  let v := native_scale_design_bounds q
  have hprec := q.valid.2.2.2.2.1
  have hloss := q.valid.2.2.2.2.2.1
  have hZ : 0 ≤ q.grid.zetaExponent := by
    rw [q.grid_zetaExponent]
    exact (mul_pos (NativeDesign.zetaCoeff_pos q.kappa1 q.dimension (Ep:=q.Ep) hprec) q.gainL_pos).le
  have hGrid := eventually_exists_original_root_grid N hN q.grid
  have hPrimitive := eventually_native_prestate_primitive_budgets N hN
    (h:=q.coefficient) (areg:=q.regularity) (E:=q.floor) (eta:=q.floorEta) (d:=q.dimension)
    v.coefficient_pos v.regularity_pos v.floor_pos q.floor_eta_pos q.valid.2.1.le
    v.coefficient_small q.floor_range
  have hSS := eventually_native_support_scalar_budgets N hN
    (e:=q.mass) (h:=q.coefficient) (ar:=q.residualRatio) (nativeMin:=q.nativeMin)
    v.mass_pos v.source_small v.native_support v.residual_support
  have hDisplay := eventually_native_qualification_display_power_budgets N hN q.degree
    v.coefficient_pos v.analyticPower_nonneg v.theta_room v.display_room
  have hFailure := eventually_native_failure_mass_bound N hN q.resLength hZ v.mass_pos
  have hSupport := eventually_original_root_support_loss_le N hN
    (h:=q.coefficient) (w:=q.coefficient) (c:=q.coefficient/1000) (t:=q.coefficient/5)
    (p:=4*q.mass) (r:=4*q.mass) (target:=2*q.mass) (margin:=q.mass/10)
    (by linarith only [v.mass_pos])
    (by linarith only [v.mass_pos,v.source_small])
    (by linarith only [v.mass_pos,v.source_small])
  have hRegularity := NativeDesign.eventually_regularity_factor_le N hN q.kappa1 q.dimension
    (Ep:=q.Ep) (precision:=q.precision) (loss:=q.loss) (gain:=q.gainL) (L:=1)
    hloss q.gainL_pos (by norm_num)
  obtain ⟨sigmaP,hSigmaP,hSigmaP1,hCharge⟩ := eventually_original_prestate_charge_le N hN q.regLength
    (h:=q.coefficient) (b:=q.regularity/1000) (eta:=q.floorEta)
    v.coefficient_pos q.floor_eta_pos q.floor_range
  obtain ⟨sigmaE,hSigmaE,hSigmaE1,hTerminal⟩ := eventually_post_state_exception_cost N hN
    v.mass_display v.mass_native
  have hSupportGap : q.mass/10 < 2*q.mass := by linarith only [v.mass_pos]
  obtain ⟨sigmaS,hSigmaS,hSigmaS1,hSupportCharge⟩ := eventually_post_state_exception_cost N hN
    hSupportGap hSupportGap
  let sigma := min sigmaP (min sigmaE sigmaS)
  have hSigma : 0 < sigma := lt_min hSigmaP (lt_min hSigmaE hSigmaS)
  have hSigmaP' : sigma ≤ sigmaP := min_le_left _ _
  have hSigmaE' : sigma ≤ sigmaE := (min_le_right _ _).trans (min_le_left _ _)
  have hSigmaS' : sigma ≤ sigmaS := (min_le_right _ _).trans (min_le_right _ _)
  let large := max ((10:ℝ)^100) (max Cmk q.threshold)
  have hLarge := ((tendsto_rpow_atTop v.coefficient_pos).comp hN).eventually_ge_atTop large
  let p0 := originalPreStateWidth q.dimension q.floorEpsilon q.regLength
  have hp0 : 0 < p0 := originalPreStateWidth_pos _ _ _
  have hStart := ((tendsto_rpow_atTop (by linarith only [v.regularity_pos] : 0 < q.regularity/1000)).comp hN).eventually_ge_atTop p0⁻¹
  refine ⟨sigma,hSigma,hSigmaP'.trans hSigmaP1,?_⟩
  filter_upwards [hN.eventually_gt_atTop 1,hGrid,hPrimitive,hSS,hDisplay,hFailure,hSupport,
    hRegularity,hCharge,hTerminal,hSupportCharge,hLarge,hStart] with
    k hk hGrid hPrimitive hSS hDisplay hFailure hSupport hRegularity hCharge hTerminal hSupportCharge hLarge hStart
  let n := N k
  have hn : 1 < n := hk
  have hnp : 0 < n := zero_lt_one.trans hn
  change large ≤ n^q.coefficient at hLarge
  change p0⁻¹ ≤ n^(q.regularity/1000) at hStart
  have h100 : (10:ℝ)^100 ≤ n^q.coefficient := (le_max_left _ _).trans hLarge
  have hH32 : 32 ≤ n^q.coefficient := (by norm_num : (32:ℝ) ≤ 10^100).trans h100
  have hH3000 : 3000 ≤ n^q.coefficient := (by norm_num : (3000:ℝ) ≤ 10^100).trans h100
  have hCmkN : Cmk ≤ n^q.coefficient := (le_max_left _ _).trans ((le_max_right _ _).trans hLarge)
  have hThreshold : q.threshold ≤ n^q.coefficient :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hLarge)
  have hSourceMass : q.coefficient ≤ q.mass/4 := by linarith only [v.source_small,v.mass_pos]
  have hRegMass : q.regularity/1000 ≤ q.mass/4 := by linarith only [v.regularity_small,v.mass_pos]
  have hCoeffReg : q.coefficient ≤ q.regularity := by linarith only [v.coefficient_small,v.regularity_pos]
  have hCoeffMass : q.coefficient ≤ q.mass := by linarith only [v.source_small,v.mass_pos]
  have hCoeffGain : q.coefficient ≤ q.gainL := by linarith only [v.clock_lip,v.mass_pos]
  have h625 : 625 ≤ n^q.mass := (by norm_num : (625:ℝ) ≤ 10^100).trans
    (h100.trans (Real.rpow_le_rpow_of_exponent_le hn.le hCoeffMass))
  have hX100 : 100 ≤ n^(q.mass/4) := (by norm_num : (100:ℝ) ≤ 10^100).trans
    (h100.trans (Real.rpow_le_rpow_of_exponent_le hn.le hSourceMass))
  have hA2 : 2 ≤ n^q.regularity := (by norm_num : (2:ℝ) ≤ 10^100).trans
    (h100.trans (Real.rpow_le_rpow_of_exponent_le hn.le hCoeffReg))
  have hMargin16 : 16 ≤ n^q.gainL := (by norm_num : (16:ℝ) ≤ 10^100).trans
    (h100.trans (Real.rpow_le_rpow_of_exponent_le hn.le hCoeffGain))
  have hp0N : n^(-(q.regularity/1000)) ≤ p0 := by
    rw [Real.rpow_neg hnp.le]
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hp0) hStart
  intro T fine steps Kcensus stripWidth theta hT hClockLo hClockHi hFine hKc hKcN hSteps hStepsN hWidth hTheta hThetaH hRemainder
  let lam := ((2:ℝ)^T)⁻¹
  let ch := nativeClockExponent n T
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hlam1 : lam ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  obtain ⟨g,hStartEq,hCut,hZlo,hZhi,hRlo,hRhi,hFloor,hLast,hRegA,hResA,hCount,hWCount⟩ :=
    hGrid T hClockLo hClockHi fine hFine
  change (2:ℝ)^g.regStep ≤ n^(q.mass/4) at hRegA
  change (2:ℝ)^g.resStep ≤ n^q.residualRatio at hResA
  change (g.floorCount:ℝ) ≤ n^q.coefficient at hCount
  change (g.W.card:ℝ) ≤ n^q.coefficient at hWCount
  rw [q.grid_start] at hStartEq
  have hFloorN : n^(-q.floor) ≤ dyadicParameterWidth g.paletteFinest :=
    (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith only [q.grid_floorExponent_le])).trans hFloor
  have hStartQuery : n^(-(q.regularity/1000)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn.le (by linarith only [v.regularity_pos])
  have hStartWidth := parameterLevel_width (n^(-(q.regularity/1000)))
    (Real.rpow_pos_of_pos hnp _) hStartQuery
  rw [←hStartEq] at hStartWidth
  have hStartP0 : dyadicParameterWidth g.floorStart ≤ p0 := hStartWidth.2.trans hp0N
  have hPrimitivePoint := hPrimitive (dyadicParameterWidth g.floorStart) hStartWidth.1 hStartWidth.2
  let H := n^q.coefficient
  let B := n^(q.regularity/1000)
  let Lp := 6*(n^(q.mass/4)+3*B)
  let etaFit := 2*((3*H+1)*Lp)*g.rho
  let graphError := n^(-q.target)
  let radius := originalPencilRadius H stripWidth
  have hH : 1 ≤ H := by dsimp only [H]; linarith only [hH32]
  have hB : 1 ≤ B := Real.one_le_rpow hn.le (by linarith only [v.regularity_pos])
  have hPower := root_geometry_constant_power hn hX100 hH hB
    (Real.rpow_le_rpow_of_exponent_le hn.le hSourceMass)
    (Real.rpow_le_rpow_of_exponent_le hn.le hRegMass)
  have hLp : 0 ≤ Lp := hPower.1
  have hLpPower : Lp ≤ n^(q.mass/2) := hPower.2.1
  have hGeometryPower : rootGeometryConstant H B Lp ≤ n^q.mass := hPower.2.2.1
  have hRowPower : 3*((3*H+1)*Lp) ≤ n^(2*q.mass) := hPower.2.2.2
  have hGeometryRoom := q.grid_geometry_room
  have hGeometry := root_geometry_small_of_power_bounds hn hGeometryPower g.rho_pos.le
    (dyadicParameterWidth_pos g.lastLevel).le (dyadicParameterWidth_pos fine).le
    hRlo hRhi hLast hFine le_rfl hGeometryRoom.1 hGeometryRoom.2.1 hGeometryRoom.2.2 hMargin16
  have hEtaCoefficient : 2*((3*H+1)*Lp) ≤ rootGeometryConstant H B Lp := by
    unfold rootGeometryConstant
    nlinarith only [hH,hB,hLp,mul_nonneg (zero_le_one.trans hH) hLp]
  have hEtaPower : etaFit ≤ n^(-2*q.thetaFloor) := by
    calc
      _ ≤ rootGeometryConstant H B Lp*g.rho := mul_le_mul_of_nonneg_right hEtaCoefficient g.rho_pos.le
      _ ≤ n^q.mass*n^(-((q.grid.rhoPower:ℝ)*q.grid.lower*q.grid.D)) :=
        mul_le_mul hGeometryPower hRhi g.rho_pos.le (by positivity)
      _ = n^(q.mass-(q.grid.rhoPower:ℝ)*q.grid.lower*q.grid.D) := by
        rw [←Real.rpow_add hnp]
        congr 1
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le (by
        change q.mass-(NativeDesign.rhoPower q.kappa1 q.Ep q.precision:ℝ)*q.gainL*
          nativeQualificationDepth q.dimension q.degree ≤ -2*q.thetaFloor
        nlinarith only [v.rho_fit])
  have hGraphPower : graphError ≤ n^(-2*q.thetaFloor) :=
    Real.rpow_le_rpow_of_exponent_le hn.le (by linarith only [v.graph_fit])
  have hNativeAnalytic := q.analytic_clock_power hn.le hClockHi
  have hDisplayPoint := hDisplay ch q.epsilon theta lam graphError etaFit
    hlam hTheta hThetaH hGraphPower hEtaPower hRemainder hNativeAnalytic
  let mesh := theta/(8*((q.degree:ℝ)+1))
  let bound : ℤ := ⌈(3*H+(1+2*H)*n^(ch*q.epsilon))/mesh⌉+2
  let duration := lam*n^(-(ch*q.epsilon))
  have hCutoff : g.zeta ≤ lam^q.cutoff := hCut.trans
    (Real.rpow_le_rpow_of_exponent_ge hlam hlam1
      (nativeQualificationCutoff_le_depth q.dimension q.degree))
  have hNativeMin : q.nativeMin ≤ ch*q.alpha := q.native_min_le_clock hClockLo
  have hQ : q.threshold ≤ n^ch := hThreshold.trans
    (Real.rpow_le_rpow_of_exponent_le hn.le (hCoeffGain.trans hClockLo))
  have hCanonical : 151200*(12*H+3)*H*(3:ℝ)^q.dimension ≤ n^q.mass :=
    native_canonical_constant_power hn hH3000 q.valid.2.1.le (by linarith only [v.source_small,v.mass_pos])
  have hNativeNum := native_numerator_power_bound hn.le v.mass_pos.le h625
    (by positivity : 0 ≤ 151200*(12*H+3)*H*(3:ℝ)^q.dimension) hCanonical
  have hWidthRaw : n^(-q.coefficient) ≤ stripWidth := hWidth
  have hWidthInv : (n^q.coefficient)⁻¹ ≤ stripWidth := by
    simpa only [Real.rpow_neg hnp.le] using hWidthRaw
  have hRadiusPoint := originalPencilRadius_bounds (H:=n^q.coefficient) (width:=stripWidth) hH32 hWidthInv
  have hRadiusLower : n^(-(q.mass/1000)) ≤ radius := by
    have hH4 : (H^4)⁻¹=n^(-4*q.coefficient) := by
      rw [show (-4*q.coefficient)=-(4*q.coefficient) by ring,Real.rpow_neg hnp.le]
      congr 1
      dsimp only [H]
      rw [←Real.rpow_mul_natCast hnp.le]
      congr 1
      ring
    calc
      _ ≤ n^(-4*q.coefficient) := Real.rpow_le_rpow_of_exponent_le hn.le
        (by linarith only [v.source_small,v.mass_pos])
      _ = (H^4)⁻¹ := hH4.symm
      _ ≤ _ := hRadiusPoint.2.2.2.2.2
  have hSSPoint := hSS (ch*q.alpha) B Cmk radius hNativeMin hB
    (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith only [v.regularity_small,v.mass_pos]))
    hCmk (hCmkN.trans (Real.rpow_le_rpow_of_exponent_le hn.le
      (by linarith only [v.source_small,v.mass_pos]))) hRadiusLower
  let s := originalRootScales_of_grid g n q.mass q.coefficient q.regularity q.floor q.target
    q.residualRatio q.dimension Cmk Kcensus stripWidth steps T q.degree q.epsilon q.cutoff q.alpha
    q.threshold mesh theta duration bound hn v.mass_pos v.coefficient_pos v.regularity_pos v.floor_pos
    v.residualRatio_nonneg v.coefficient_small (by linarith only [v.regularity_small,v.mass_pos])
    v.graph_room hH32 hA2 q.valid.1 q.valid.2.1.le hKc hSteps hCmk hMK hWidth hFloorN hRegA hResA
    hGeometry.1 hGeometry.2.1 hGeometry.2.2 hRowPower
    (by linarith only [v.native_support,hNativeMin,v.mass_pos])
    v.qualification v.alpha_pos.le hQ hT hCutoff hNativeNum
    hSSPoint.1 hSSPoint.2.1 hSSPoint.2.2.1 hSSPoint.2.2.2
    hDisplayPoint.1 hDisplayPoint.2.2.1 hDisplayPoint.2.2.2.1 le_rfl
  have hsLength : s.regLength=q.regLength := rfl
  have hsStart : s.floorStart=g.floorStart := rfl
  have hsDimension : s.dimension=q.dimension := rfl
  have hsAreg : s.Areg=n^q.regularity := rfl
  have hsEta : originalPreStateEta s.dimension s.floorExponent s.regLength=q.floorEta := by
    change originalPreStateEta q.dimension (q.regularity/(10000*q.floor)) q.regLength=q.floorEta
    rw [q.floor_epsilon_eq]
    rfl
  have hsWidth : originalPreStateWidth s.dimension s.floorExponent s.regLength=p0 := by
    change originalPreStateWidth q.dimension (q.regularity/(10000*q.floor)) q.regLength=p0
    rw [q.floor_epsilon_eq]
  let ps := originalPreStateScales_of_power_budgets s n q.coefficient q.regularity q.floor q.target
    hn v.coefficient_pos v.regularity_pos v.floor_pos q.valid.2.1 rfl rfl rfl rfl
    g.floorCount_pos g.floorFinest g.floorResolved hFloorN hFine v.graph_room hH32
    (by simpa only [hsWidth,hsStart] using hStartP0)
    (by rw [hsEta]; simpa only [hsStart,hsDimension,n] using hPrimitivePoint.1)
    (by rw [hsEta]; simpa only [hsStart,hsDimension,n] using hPrimitivePoint.2.1)
    (by rw [hsEta]; simpa only [hsStart,hsDimension,n] using hPrimitivePoint.2.2.1)
    (fun w hw => hPrimitivePoint.2.2.2 w _ hw le_rfl)
  have hRegularityPoint := hRegularity (n^q.regularity)
    (Real.one_le_rpow hn.le v.regularity_pos.le) (by simp only [mul_one]; rfl)
  have hFactorEq : s.regularityFactor=regularityMassFactor (n^q.regularity) q.regLength := by
    simp only [OriginalRootScales.regularityFactor,regularityMassFactor,hsLength,hsAreg,Nat.cast_mul,Nat.cast_pow]
  have hFactorPos : 0 < s.regularityFactor := by simpa only [hFactorEq,NativeScaleDesign.regLength,n] using hRegularityPoint.1
  have hFactorTop : s.regularityFactor ≠ ⊤ := by simpa only [hFactorEq,NativeScaleDesign.regLength,n] using hRegularityPoint.2.1
  have hFactorPower : s.regularityFactor ≤ ENNReal.ofReal (n^(q.mass/10)) := by
    simpa only [hFactorEq,NativeScaleDesign.mass,NativeScaleDesign.regLength,mul_one,n] using hRegularityPoint.2.2
  have hHMass : H ≤ n^q.mass := Real.rpow_le_rpow_of_exponent_le hn.le hCoeffMass
  have hCanonicalS : s.canonicalConstant ≤ s.incidence.N^q.mass := hCanonical
  have hFailurePower : s.nativeFailureBound ≤ ENNReal.ofReal (n^(-q.mass)) :=
    hFailure s rfl le_rfl hZlo hHMass hCanonicalS hHMass le_rfl le_rfl rfl
      (fun _ _ => rfl) (fun _ _ => rfl) rfl (v.native_mass.trans hNativeMin)
  have hRateEq : s.rate=n^(-(4*q.mass)) := by
    change n^(-4*q.mass)=n^(-(4*q.mass))
    congr 1
    ring
  have hSupportPower : s.supportLoss ≤ ENNReal.ofReal (n^(-2*q.mass)) := by
    simpa only [neg_mul,n] using hSupport s le_rfl hWCount hKcN hStepsN le_rfl hRateEq.le
  have hChargePoint := hCharge s ps rfl hsEta hsLength.le le_rfl hKcN hStepsN hCount
    hStartWidth.2 (fun _ => le_rfl)
  have hThetaLarge : 8 ≤ n^q.thetaFloor := (by norm_num : (8:ℝ) ≤ 10^100).trans
    (h100.trans (Real.rpow_le_rpow_of_exponent_le hn.le
      (by linarith only [v.theta_room,v.coefficient_pos])))
  have hLipRho : s.Lp*s.ρ ≤ theta/8 := by
    have hcoefficient : 1 ≤ 2*(3*H+1) := by linarith only [hH]
    have hdom : Lp*g.rho ≤ etaFit := by
      have hh := mul_le_mul_of_nonneg_right hcoefficient (mul_nonneg hLp g.rho_pos.le)
      dsimp only [etaFit]
      nlinarith only [hh]
    change Lp*g.rho ≤ theta/8
    calc
      _ ≤ n^(-2*q.thetaFloor) := hdom.trans hEtaPower
      _ = n^(-q.thetaFloor)/n^q.thetaFloor := by
        rw [←Real.rpow_sub hnp]
        congr 1
        ring
      _ ≤ n^(-q.thetaFloor)/8 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hThetaLarge
      _ ≤ _ := div_le_div_of_nonneg_right hTheta (by norm_num)
  have hLipClock : s.Lp*((2:ℝ)^T)⁻¹ ≤ 1/8 := by
    change Lp*lam ≤ 1/8
    calc
      _ ≤ n^(q.mass/2)*n^(-ch) := mul_le_mul hLpPower
        (le_of_eq (nativeClockExponent_width hn T).symm) (by positivity) (by positivity)
      _ = n^(q.mass/2-ch) := by rw [←Real.rpow_add hnp] <;> congr 1 <;> ring
      _ ≤ n^(-q.coefficient) := Real.rpow_le_rpow_of_exponent_le hn.le
        (by linarith only [v.clock_lip,hClockLo])
      _ = (n^q.coefficient)⁻¹ := Real.rpow_neg hnp.le _
      _ ≤ 1/8 := by
        have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8)
          ((by norm_num : (8:ℝ) ≤ 10^100).trans h100)
        simpa only [one_div] using hh
  refine ⟨{
    scales := s
    pre := ps
    b_eq := rfl
    N_eq := rfl
    M_eq := rfl
    T_eq := rfl
    dimension_eq := rfl
    H_eq := rfl
    B_eq := rfl
    U_eq := rfl
    fitError_eq := rfl
    Cpure_eq := rfl
    Cband_eq := rfl
    Cstate_eq := rfl
    failure_eq := rfl
    stripWidth_eq := rfl
    Kcensus_eq := rfl
    steps_eq := rfl
    resolution_eq := rfl
    paletteWidth_lower := hFloorN
    floorStartWidth_upper := hStartWidth.2
    Lp_bound := hLpPower
    lipRho_small := hLipRho
    lipClock_small := hLipClock
    regularity_pos := hFactorPos
    regularity_ne_top := hFactorTop
    regularity_power := hFactorPower
    native_power := hFailurePower
    support_power := hSupportPower
    pre_charge := ?_
    terminal_charge := ?_
    support_charge := ?_
    qbound_nonneg := hDisplayPoint.2.1
    qcoefficient_cost := hDisplayPoint.2.2.2.2.1
    qerror_eq := rfl
    qduration_min := hDisplayPoint.2.2.2.2.2
  }⟩
  · intro kappa hkappa hkappaN
    exact hChargePoint kappa hkappa (hkappaN.trans
      (Real.rpow_le_rpow_of_exponent_le hn.le hSigmaP'))
  · intro kappa hkappa hkappaN
    exact hTerminal kappa hkappa (hkappaN.trans
      (Real.rpow_le_rpow_of_exponent_le hn.le hSigmaE')) _ _ hFactorPower hFailurePower
  · intro kappa hkappa hkappaN
    have hh := hSupportCharge kappa hkappa (hkappaN.trans
      (Real.rpow_le_rpow_of_exponent_le hn.le hSigmaS')) s.regularityFactor s.supportLoss hFactorPower
      (by simpa only [neg_mul,n] using hSupportPower)
    apply le_trans _ hh
    apply mul_le_mul' le_rfl
    have hmult : s.supportLoss ≤ (10000:ENNReal)*s.supportLoss := by
      simpa only [one_mul] using mul_le_mul' (by norm_num : (1:ENNReal) ≤ 10000)
        (le_refl s.supportLoss)
    exact hmult.trans (le_add_left le_rfl)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
