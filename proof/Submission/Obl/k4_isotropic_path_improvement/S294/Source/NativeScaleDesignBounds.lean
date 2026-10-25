-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeScaleDesignBounds, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleData

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.Qualification.Jets2
open Parent.Qualification.PhysicalModel

noncomputable section

structure NativeScaleDesignBounds (q : NativeScaleDesign) : Prop where
  mass_pos : 0 < q.mass
  coefficient_pos : 0 < q.coefficient
  regularity_pos : 0 < q.regularity
  floor_pos : 0 < q.floor
  target_pos : 0 < q.target
  residualRatio_nonneg : 0 ≤ q.residualRatio
  display_pos : 0 < q.display
  thetaFloor_pos : 0 < q.thetaFloor
  epsilon_pos : 0 < q.epsilon
  alpha_pos : 0 < q.alpha
  degree_two : 2 ≤ q.degree
  coefficient_small : q.coefficient ≤ q.regularity/100000000
  regularity_small : q.regularity ≤ q.mass/400
  source_small : q.coefficient ≤ q.mass/1000000
  mass_display : q.mass/10 < q.display
  mass_native : q.mass/10 < q.mass
  analyticPower_nonneg : 0 ≤ q.analyticPower
  display_room : 2*q.coefficient+q.analyticPower ≤ q.display
  theta_room : 4*q.coefficient ≤ q.thetaFloor
  graph_fit : 2*q.thetaFloor ≤ q.target
  rho_fit : q.mass+2*q.thetaFloor ≤
    (NativeDesign.rhoPower q.kappa1 q.Ep q.precision:ℝ)*
      nativeQualificationDepth q.dimension q.degree*q.gainL
  graph_room : q.floor+2*q.coefficient ≤ q.target
  native_mass : (200*(q.resLength:ℝ)+100)*q.mass ≤ q.nativeMin
  native_support : 100*q.mass ≤ q.nativeMin
  residual_support : 8*q.residualRatio ≤ q.nativeMin
  clock_lip : q.mass/2+q.coefficient ≤ q.gainL
  qualification : NativeQualificationAt q.dimension q.degree q.epsilon q.cutoff q.alpha q.threshold

/-- All fixed comparisons of the concrete native scale design are
proved before every sample and all original data. -/
theorem native_scale_design_bounds (q : NativeScaleDesign) : NativeScaleDesignBounds q := by
  have hp := q.valid.2.2.2.2.1
  have hl := q.valid.2.2.2.2.2.1
  have hl1 := q.valid.2.2.2.2.2.2
  have hκ := q.valid.2.2.1
  have he := NativeDesign.massCoeff_pos q.kappa1 q.dimension (Ep:=q.Ep) (precision:=q.precision) hl
  have hh := NativeDesign.coefficientCoeff_pos q.kappa1 q.dimension (Ep:=q.Ep) (precision:=q.precision) hl
  have ha := NativeDesign.regularityCoeff_pos q.kappa1 q.dimension (Ep:=q.Ep) (precision:=q.precision) hl
  have hE := NativeDesign.floorEndCoeff_pos q.kappa1 q.dimension (Ep:=q.Ep) hp
  have hC := NativeDesign.clockCoeff_pos (Ep:=q.Ep) hp
  have heps : 0 < q.epsilon := NativeDesign.analyticEpsilon_pos hp hl
  have halpha : 0 < q.alpha := nativeQualificationExponent_pos _ _ _
  have hM : 2 ≤ q.degree := by
    have hc : 0 < ⌈8/q.kappa1⌉₊ := Nat.ceil_pos.mpr (div_pos (by norm_num) hκ)
    change 2 ≤ qualDegree q.kappa1
    unfold qualDegree
    omega
  have hr := NativeDesign.native_display_exponent_room (Ep:=q.Ep) q.valid
  have hreg := NativeDesign.regularityCoeff_le_mass q.kappa1 q.dimension
    (Ep:=q.Ep) (precision:=q.precision) hl
  have hsmall := NativeDesign.coefficient_le_regularity q.kappa1 q.dimension
    (Ep:=q.Ep) (precision:=q.precision) hl
  have hcoeffMass := NativeDesign.coefficient_le_mass_quarter q.kappa1 q.dimension
    (Ep:=q.Ep) (precision:=q.precision) hl
  have he1 := NativeDesign.massCoeff_le_one q.kappa1 q.dimension
    (Ep:=q.Ep) (precision:=q.precision) hl1
  have hmassDisplay := NativeDesign.massCoeff_display_le q.kappa1 q.dimension
    (Ep:=q.Ep) (precision:=q.precision) hl
  have hMass := NativeDesign.native_mass_room q.kappa1 q.dimension
    (Ep:=q.Ep) (precision:=q.precision) hl
  have hqual := (nativeQualificationParameters_spec q.dimension q.degree q.epsilon
    q.valid.1 q.valid.2.1 hM heps).2
  have hdisplay : 0 < NativeDesign.displayCoeff q.Ep q.loss := by unfold NativeDesign.displayCoeff; positivity
  have hg := q.gainL_pos
  have heG := mul_pos he hg
  have heqG : 0 < q.mass := heG
  have hhG := mul_pos hh hg
  have haG := mul_pos ha hg
  have hEG := mul_pos hE hg
  have hDisplayG := mul_pos hdisplay hg
  have hScalarSource : NativeDesign.coefficientCoeff q.kappa1 q.dimension q.Ep q.precision q.loss ≤
      NativeDesign.massCoeff q.kappa1 q.dimension q.Ep q.precision q.loss/1000000 := by
    linarith only [hsmall,hreg,he]
  have hNativeMass := mul_le_mul_of_nonneg_right hMass hg.le
  have hresLength : (0:ℝ) ≤ q.resLength := Nat.cast_nonneg _
  refine {
    mass_pos := heG
    coefficient_pos := hhG
    regularity_pos := haG
    floor_pos := hEG
    target_pos := ?_
    residualRatio_nonneg := ?_
    display_pos := hDisplayG
    thetaFloor_pos := mul_pos hr.1 hg
    epsilon_pos := heps
    alpha_pos := halpha
    degree_two := hM
    coefficient_small := ?_
    regularity_small := ?_
    source_small := ?_
    mass_display := ?_
    mass_native := by change q.mass/10 < q.mass; linarith only [heqG]
    analyticPower_nonneg := ?_
    display_room := ?_
    theta_room := ?_
    graph_fit := ?_
    rho_fit := ?_
    graph_room := ?_
    native_mass := ?_
    native_support := ?_
    residual_support := by unfold NativeScaleDesign.residualRatio NativeScaleDesign.nativeMin; linarith
    clock_lip := ?_
    qualification := hqual
  }
  · exact (mul_pos hr.1 hg).trans_le (by
      have hh' := mul_le_mul_of_nonneg_right hr.2.2.2.1 hg.le
      change NativeDesign.thetaFloorCoeff q.kappa1 q.Ep q.precision*q.gainL ≤
        NativeDesign.graphTargetCoeff q.kappa1 q.dimension q.Ep q.precision*q.gainL
      nlinarith only [hh',mul_pos hr.1 hg])
  · unfold NativeScaleDesign.residualRatio
    have hA := NativeDesign.alphaBudget_pos q.kappa1 q.dimension q.Ep q.precision q.loss
    positivity
  · have hh' := mul_le_mul_of_nonneg_right hsmall hg.le
    change _ ≤ _
    unfold NativeScaleDesign.coefficient NativeScaleDesign.regularity
    nlinarith only [hh']
  · have hh' := mul_le_mul_of_nonneg_right hreg hg.le
    unfold NativeScaleDesign.regularity NativeScaleDesign.mass
    nlinarith only [hh']
  · have hh' := mul_le_mul_of_nonneg_right hScalarSource hg.le
    unfold NativeScaleDesign.coefficient NativeScaleDesign.mass
    nlinarith only [hh']
  · have hh' := mul_le_mul_of_nonneg_right hmassDisplay hg.le
    unfold NativeScaleDesign.mass NativeScaleDesign.display
    nlinarith only [hh',hDisplayG]
  · unfold NativeScaleDesign.analyticPower NativeDesign.analyticPowerCoeff
    exact mul_nonneg (mul_nonneg hC.le heps.le) hg.le
  · have hh' := mul_le_mul_of_nonneg_right hr.2.2.1 hg.le
    unfold NativeScaleDesign.coefficient NativeScaleDesign.analyticPower NativeScaleDesign.display
    nlinarith only [hh']
  · have hh' := mul_le_mul_of_nonneg_right hr.2.1 hg.le
    unfold NativeScaleDesign.coefficient NativeScaleDesign.thetaFloor
    nlinarith only [hh']
  · have hh' := mul_le_mul_of_nonneg_right hr.2.2.2.1 hg.le
    unfold NativeScaleDesign.thetaFloor NativeScaleDesign.target
    nlinarith only [hh']
  · have hh' := mul_le_mul_of_nonneg_right hr.2.2.2.2.1 hg.le
    unfold NativeScaleDesign.mass NativeScaleDesign.thetaFloor NativeScaleDesign.degree
    nlinarith only [hh']
  · have hh' := mul_le_mul_of_nonneg_right hr.2.2.2.2.2.1 hg.le
    unfold NativeScaleDesign.floor NativeScaleDesign.coefficient NativeScaleDesign.target
    nlinarith only [hh']
  · simpa only [NativeScaleDesign.mass,NativeScaleDesign.nativeMin,NativeScaleDesign.resLength,mul_assoc]
      using hNativeMass
  · have hh' : (200*(q.resLength:ℝ)+100)*q.mass ≤ q.nativeMin := by
      simpa only [NativeScaleDesign.mass,NativeScaleDesign.nativeMin,NativeScaleDesign.resLength,mul_assoc]
        using hNativeMass
    nlinarith only [hh',hresLength,heqG]
  · have hh' := mul_le_mul_of_nonneg_right hcoeffMass hg.le
    have he' := mul_le_mul_of_nonneg_right he1 hg.le
    unfold NativeScaleDesign.mass NativeScaleDesign.coefficient
    nlinarith only [hh',he',hg]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
