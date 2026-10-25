-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeScaleData, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDisplayProfile
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalPreStateScaleAssembly

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.Qualification
open Parent.Qualification.Jets2
open Parent.Qualification.PhysicalModel
open scoped ENNReal

noncomputable section

/-- All fixed inputs of the native scalar design precede the sample
and every original incidence source. -/
structure NativeScaleDesign where
  kappa1 : ℝ
  dimension : ℝ
  Ep : ℕ
  precision : ℝ
  loss : ℝ
  gainL : ℝ
  valid : NativeDesign.Valid kappa1 dimension precision loss
  gainL_pos : 0 < gainL

namespace NativeScaleDesign

def mass (q : NativeScaleDesign) : ℝ :=
  NativeDesign.massCoeff q.kappa1 q.dimension q.Ep q.precision q.loss*q.gainL
def coefficient (q : NativeScaleDesign) : ℝ :=
  NativeDesign.coefficientCoeff q.kappa1 q.dimension q.Ep q.precision q.loss*q.gainL
def regularity (q : NativeScaleDesign) : ℝ :=
  NativeDesign.regularityCoeff q.kappa1 q.dimension q.Ep q.precision q.loss*q.gainL
def floor (q : NativeScaleDesign) : ℝ :=
  NativeDesign.floorEndCoeff q.kappa1 q.dimension q.Ep q.precision*q.gainL
def target (q : NativeScaleDesign) : ℝ :=
  NativeDesign.graphTargetCoeff q.kappa1 q.dimension q.Ep q.precision*q.gainL
def residualRatio (q : NativeScaleDesign) : ℝ :=
  NativeDesign.alphaBudget q.kappa1 q.dimension q.Ep q.precision q.loss*q.gainL/8
def display (q : NativeScaleDesign) : ℝ := NativeDesign.displayCoeff q.Ep q.loss*q.gainL
def analyticPower (q : NativeScaleDesign) : ℝ :=
  NativeDesign.analyticPowerCoeff q.Ep q.precision q.loss*q.gainL
def thetaFloor (q : NativeScaleDesign) : ℝ :=
  NativeDesign.thetaFloorCoeff q.kappa1 q.Ep q.precision*q.gainL
def degree (q : NativeScaleDesign) : ℕ := qualDegree q.kappa1
def epsilon (q : NativeScaleDesign) : ℝ := NativeDesign.analyticEpsilon q.Ep q.precision q.loss
def alpha (q : NativeScaleDesign) : ℝ :=
  nativeQualificationExponent q.dimension q.degree q.epsilon
def cutoff (q : NativeScaleDesign) : ℝ := nativeQualificationCutoff q.dimension q.degree
def threshold (q : NativeScaleDesign) : ℝ := nativeQualificationThreshold q.dimension q.degree q.epsilon
def nativeMin (q : NativeScaleDesign) : ℝ :=
  NativeDesign.alphaBudget q.kappa1 q.dimension q.Ep q.precision q.loss*q.gainL
def floorEpsilon (q : NativeScaleDesign) : ℝ :=
  NativeDesign.floorEpsilon q.kappa1 q.dimension q.Ep q.precision q.loss
def floorEta (q : NativeScaleDesign) : ℝ :=
  NativeDesign.floorEta q.kappa1 q.dimension q.Ep q.precision q.loss
def regLength (q : NativeScaleDesign) : ℕ :=
  NativeDesign.regularityLength q.kappa1 q.dimension q.Ep q.precision q.loss
def resLength (q : NativeScaleDesign) : ℕ :=
  NativeDesign.residualLength q.kappa1 q.dimension q.Ep q.precision q.loss
def grid (q : NativeScaleDesign) : OriginalRootGridPowers :=
  NativeDesign.nativeGridProfile (Ep:=q.Ep) q.valid q.gainL_pos

/-- The exponent used in `Lp_bound` fits the middle-level clock gap. -/
theorem mass_half_le_clock (q : NativeScaleDesign) : q.mass/2 ≤ q.kappa1*q.gainL/8 := by
  have hh := NativeDesign.massCoeff_le_kappa q.dimension (Ep:=q.Ep) (precision:=q.precision)
    q.valid.2.2.1 q.valid.2.2.2.1 q.valid.2.2.2.2.2.2
  have h := mul_le_mul_of_nonneg_right hh q.gainL_pos.le
  have hk : 0 < q.kappa1*q.gainL := mul_pos q.valid.2.2.1 q.gainL_pos
  unfold mass
  nlinarith only [h,hk]

end NativeScaleDesign

/-- Concrete numerical choices and all consumer budgets of one native
sample. This package contains no source, prior, row, coefficient
table, palette, support selection or qualification certificate. -/
structure NativeScaleData (q : NativeScaleDesign) (N sigma : ℝ)
    (T fine steps : ℕ) (Kcensus stripWidth theta : ℝ) where
  scales : OriginalRootScales
  pre : OriginalPreStateScales scales
  b_eq : scales.b=dyadicParameterWidth fine
  N_eq : scales.incidence.N=N
  M_eq : scales.incidence.M=q.degree
  T_eq : scales.T=T
  dimension_eq : scales.dimension=q.dimension
  H_eq : scales.H=N^q.coefficient
  B_eq : scales.B=N^(q.regularity/1000)
  U_eq : scales.Uvelocity=N^q.coefficient
  fitError_eq : scales.error=N^(-q.target)
  Cpure_eq : scales.Cpure=N^q.coefficient
  Cband_eq : scales.Cband=N^q.coefficient
  Cstate_eq : scales.incidence.Cstate=N^q.coefficient
  failure_eq : scales.failure=1/2
  stripWidth_eq : scales.stripWidth=stripWidth
  Kcensus_eq : scales.Kcensus=Kcensus
  steps_eq : scales.steps=steps
  resolution_eq : scales.resolution=dyadicParameterWidth fine/(2:ℝ)^steps
  paletteWidth_lower : N^(-q.floor) ≤ dyadicParameterWidth scales.paletteFinest
  floorStartWidth_upper : dyadicParameterWidth scales.floorStart ≤ N^(-(q.regularity/1000))
  Lp_bound : scales.Lp ≤ N^(q.mass/2)
  lipRho_small : scales.Lp*scales.ρ ≤ theta/8
  lipClock_small : scales.Lp*((2:ℝ)^T)⁻¹ ≤ 1/8
  regularity_pos : 0 < scales.regularityFactor
  regularity_ne_top : scales.regularityFactor ≠ ⊤
  regularity_power : scales.regularityFactor ≤ ENNReal.ofReal (N^(q.mass/10))
  native_power : scales.nativeFailureBound ≤ ENNReal.ofReal (N^(-q.mass))
  support_power : scales.supportLoss ≤ ENNReal.ofReal (N^(-2*q.mass))
  pre_charge : ∀ kappa : ℝ, 1 ≤ kappa → kappa ≤ N^sigma →
    pre.charge ≤ ENNReal.ofReal (kappa⁻¹/64)
  terminal_charge : ∀ kappa : ℝ, 1 ≤ kappa → kappa ≤ N^sigma →
    scales.regularityFactor*(ENNReal.ofReal (2/N^q.display)+10000*scales.nativeFailureBound) ≤
      ENNReal.ofReal (kappa⁻¹/1024)
  support_charge : ∀ kappa : ℝ, 1 ≤ kappa → kappa ≤ N^sigma →
    scales.regularityFactor*scales.supportLoss ≤ ENNReal.ofReal (kappa⁻¹/1024)
  qbound_nonneg : 0 ≤ scales.bound
  qcoefficient_cost : Parent.QualificationClock.coefficientCost q.degree*
    (scales.mesh*(scales.bound:ℝ)) ≤ N^q.display
  qerror_eq : scales.err=theta
  qduration_min : 1/N^q.display ≤ scales.duration/((2:ℝ)^T)⁻¹

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
