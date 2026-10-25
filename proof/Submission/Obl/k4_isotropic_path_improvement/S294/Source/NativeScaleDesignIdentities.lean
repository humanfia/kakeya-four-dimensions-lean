-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeScaleDesignIdentities, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleDesignBounds

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleDesign

open Parent.Qualification.Jets2
open Parent.Qualification.PhysicalModel

noncomputable section

theorem grid_zetaExponent (q : NativeScaleDesign) :
    q.grid.zetaExponent=NativeDesign.zetaCoeff q.kappa1 q.dimension q.Ep q.precision*q.gainL :=
  NativeDesign.nativeGridProfile_zetaExponent q.valid q.gainL_pos

theorem grid_rhoExponent (q : NativeScaleDesign) :
    q.grid.rhoExponent=NativeDesign.rhoCoeff q.kappa1 q.dimension q.Ep q.precision*q.gainL :=
  NativeDesign.nativeGridProfile_rhoExponent q.valid q.gainL_pos

theorem grid_floorExponent_le (q : NativeScaleDesign) : q.grid.floorExponent ≤ q.floor :=
  NativeDesign.nativeGridProfile_floorExponent_le q.valid q.gainL_pos

theorem grid_start (q : NativeScaleDesign) : q.grid.start=q.regularity/1000 := by
  change (NativeDesign.regularityCoeff q.kappa1 q.dimension q.Ep q.precision q.loss/1000)*q.gainL=_
  unfold regularity
  ring

theorem grid_count (q : NativeScaleDesign) : q.grid.count=q.coefficient := rfl
theorem grid_target (q : NativeScaleDesign) : q.grid.target=q.target := rfl
theorem grid_regRatio (q : NativeScaleDesign) : q.grid.regRatio=q.mass/4 := rfl
theorem grid_resRatio (q : NativeScaleDesign) : q.grid.resRatio=q.residualRatio := rfl
theorem grid_regLength (q : NativeScaleDesign) : q.grid.regIntervals+1=q.regLength := rfl
theorem grid_resLength (q : NativeScaleDesign) : q.grid.resIntervals+1=q.resLength := rfl

theorem floor_epsilon_eq (q : NativeScaleDesign) :
    q.regularity/(10000*q.floor)=q.floorEpsilon :=
  NativeDesign.native_floor_epsilon_at_gain q.valid.2.2.2.2.1 q.gainL_pos

theorem floor_eta_pos (q : NativeScaleDesign) : 0 < q.floorEta :=
  originalPreStateEta_pos _ _ _

theorem floor_range (q : NativeScaleDesign) :
    100000*q.coefficient ≤ (q.regularity/1000)*q.floorEta := by
  have hh := mul_le_mul_of_nonneg_right (NativeDesign.coefficient_floor_room q.kappa1 q.dimension
    (Ep:=q.Ep) (precision:=q.precision) q.valid.2.2.2.2.2.1) q.gainL_pos.le
  dsimp only [NativeDesign.floorStartCoeff] at hh
  unfold coefficient regularity floorEta
  nlinarith only [hh]

theorem native_min_le_clock {q : NativeScaleDesign} {N : ℝ} {T : ℕ}
    (hclock : q.gainL ≤ nativeClockExponent N T) :
    q.nativeMin ≤ nativeClockExponent N T*q.alpha := by
  have hbudget := nativeQualificationBudget_le_exponent q.dimension q.degree q.epsilon
  have hA : 0 ≤ q.alpha := (nativeQualificationExponent_pos _ _ _).le
  calc
    _ ≤ q.alpha*q.gainL := mul_le_mul_of_nonneg_right hbudget q.gainL_pos.le
    _ ≤ q.alpha*nativeClockExponent N T := mul_le_mul_of_nonneg_left hclock hA
    _ = _ := mul_comm _ _

theorem analytic_clock_power {q : NativeScaleDesign} {N : ℝ} {T : ℕ}
    (hN : 1 ≤ N)
    (hclock : nativeClockExponent N T ≤ NativeDesign.clockCoeff q.Ep q.precision*q.gainL) :
    N^(nativeClockExponent N T*q.epsilon) ≤ N^q.analyticPower := by
  have heps : 0 ≤ q.epsilon :=
    (NativeDesign.analyticEpsilon_pos q.valid.2.2.2.2.1 q.valid.2.2.2.2.2.1).le
  apply Real.rpow_le_rpow_of_exponent_le hN
  have hh := mul_le_mul_of_nonneg_right hclock heps
  unfold analyticPower NativeDesign.analyticPowerCoeff epsilon
  dsimp only [epsilon] at hh
  nlinarith only [hh]

theorem grid_geometry_room (q : NativeScaleDesign) :
    q.mass+(q.grid.zetaExponent+q.gainL) ≤
        (q.grid.rhoPower:ℝ)*q.grid.lower*q.grid.D ∧
      q.mass+q.grid.rhoExponent+(q.grid.zetaExponent+q.gainL) ≤ q.target ∧
      q.gainL+q.grid.rhoExponent+(q.grid.zetaExponent+q.gainL) ≤ q.target := by
  have hh := NativeDesign.native_geometry_exponent_room (Ep:=q.Ep) q.valid
  have h1 := mul_le_mul_of_nonneg_right hh.1 q.gainL_pos.le
  have h2 := mul_le_mul_of_nonneg_right hh.2.1 q.gainL_pos.le
  have h3 := mul_le_mul_of_nonneg_right hh.2.2 q.gainL_pos.le
  rw [grid_zetaExponent,grid_rhoExponent]
  change _ ≤ (NativeDesign.rhoPower q.kappa1 q.Ep q.precision:ℝ)*q.gainL*
    nativeQualificationDepth q.dimension (qualDegree q.kappa1) ∧ _ ∧ _
  unfold mass target
  constructor
  · nlinarith only [h1]
  constructor
  · nlinarith only [h2]
  · nlinarith only [h3]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleDesign
