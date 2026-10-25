-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeDisplayProfile, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeGeometryProfile

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign

open Parent.Qualification.Jets2

noncomputable section

def thetaFloorCoeff (κ₁ : ℝ) (Ep : ℕ) (precision : ℝ) : ℝ :=
  3*(((Ep:ℝ)+1)*precision+3)/κ₁

def displayCoeff (Ep : ℕ) (loss : ℝ) : ℝ := loss/((Ep:ℝ)+1)

def analyticPowerCoeff (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  clockCoeff Ep precision*analyticEpsilon Ep precision loss

theorem analyticPowerCoeff_eq {Ep : ℕ} {precision loss : ℝ} (hprecision : 1 ≤ precision) :
    analyticPowerCoeff Ep precision loss=displayCoeff Ep loss/1000000 := by
  have hC := clockCoeff_pos (Ep:=Ep) hprecision
  unfold analyticPowerCoeff analyticEpsilon displayCoeff
  field_simp <;> ring

theorem massCoeff_display_le (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ} (hloss : 0 < loss) :
    massCoeff κ₁ d₁ Ep precision loss ≤ displayCoeff Ep loss/100000000 := by
  have hd : 0 < displayCoeff Ep loss := by unfold displayCoeff; positivity
  have hL : (0:ℝ) ≤ residualLength κ₁ d₁ Ep precision loss := Nat.cast_nonneg _
  calc
    _ ≤ min (loss/((Ep:ℝ)+1)) (alphaBudget κ₁ d₁ Ep precision loss)/
        (100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1)) := massCoeff_le_unscaled κ₁ d₁ hloss
    _ ≤ displayCoeff Ep loss/(100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1)) :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hd.le (by norm_num) (by nlinarith)

theorem native_display_exponent_room {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss : ℝ}
    (hv : Valid κ₁ d₁ precision loss) :
    0 < thetaFloorCoeff κ₁ Ep precision ∧
      4*coefficientCoeff κ₁ d₁ Ep precision loss ≤ thetaFloorCoeff κ₁ Ep precision ∧
      2*coefficientCoeff κ₁ d₁ Ep precision loss+analyticPowerCoeff Ep precision loss ≤ displayCoeff Ep loss ∧
      2*thetaFloorCoeff κ₁ Ep precision ≤ graphTargetCoeff κ₁ d₁ Ep precision ∧
      massCoeff κ₁ d₁ Ep precision loss+2*thetaFloorCoeff κ₁ Ep precision ≤
        (rhoPower κ₁ Ep precision:ℝ)*nativeQualificationDepth d₁ (qualDegree κ₁) ∧
      floorEndCoeff κ₁ d₁ Ep precision+2*coefficientCoeff κ₁ d₁ Ep precision loss ≤
        graphTargetCoeff κ₁ d₁ Ep precision ∧
      4*coefficientCoeff κ₁ d₁ Ep precision loss ≤ massCoeff κ₁ d₁ Ep precision loss/1000 := by
  have hκ := hv.2.2.1
  have hκ1 := hv.2.2.2.1
  have hprecision := hv.2.2.2.2.1
  have hloss := hv.2.2.2.2.2.1
  have hloss1 := hv.2.2.2.2.2.2
  have hC : 16 ≤ clockCoeff Ep precision := by
    have hh : (1:ℝ) ≤ ((Ep:ℝ)+1)*precision :=
      one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α:=ℝ) Ep; linarith) hprecision
    unfold clockCoeff
    linarith
  have hRatio : 16 ≤ clockCoeff Ep precision/κ₁ := by
    apply (le_div_iff₀ hκ).mpr
    nlinarith only [hC,hκ1]
  have hThetaEq : thetaFloorCoeff κ₁ Ep precision=(3/4:ℝ)*(clockCoeff Ep precision/κ₁) := by
    unfold thetaFloorCoeff clockCoeff
    ring
  have hTheta : 12 ≤ thetaFloorCoeff κ₁ Ep precision := by rw [hThetaEq]; linarith
  have hm := massCoeff_le_one κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss1
  have hh := coefficient_le_mass_quarter κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hhreg := coefficient_le_regularity κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hreg := regularityCoeff_le_mass κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hmass := massCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hmassDisplay := massCoeff_display_le κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hdisplay : 0 < displayCoeff Ep loss := by unfold displayCoeff; positivity
  have han := analyticPowerCoeff_eq (loss:=loss) (Ep:=Ep) hprecision
  have hFloor := floorEndCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  have hFloor4 : 4 ≤ floorEndCoeff κ₁ d₁ Ep precision := by
    have hr := rhoCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
    have hz := zetaCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
    unfold floorEndCoeff
    linarith
  have hGraph : 16*floorEndCoeff κ₁ d₁ Ep precision+16*(clockCoeff Ep precision/κ₁)=
      graphTargetCoeff κ₁ d₁ Ep precision := by unfold graphTargetCoeff; ring
  have hP : 100*(clockCoeff Ep precision/κ₁) ≤ (rhoPower κ₁ Ep precision:ℝ) := by
    have hc := Nat.le_ceil (100*clockCoeff Ep precision/κ₁)
    unfold rhoPower
    push_cast
    simp only [div_eq_mul_inv,mul_assoc] at hc ⊢
    linarith
  have hP0 : (0:ℝ) ≤ rhoPower κ₁ Ep precision := Nat.cast_nonneg _
  have hPD : (rhoPower κ₁ Ep precision:ℝ) ≤
      (rhoPower κ₁ Ep precision:ℝ)*nativeQualificationDepth d₁ (qualDegree κ₁) :=
    le_mul_of_one_le_right hP0 (one_le_nativeQualificationDepth _ _)
  refine ⟨by linarith,by linarith,?_,?_,?_,?_,by linarith⟩
  · rw [han]
    linarith
  · rw [hThetaEq]
    linarith
  · rw [hThetaEq]
    linarith
  · linarith

theorem native_floor_epsilon_at_gain {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss gainL : ℝ}
    (hprecision : 1 ≤ precision) (hg : 0 < gainL) :
    (regularityCoeff κ₁ d₁ Ep precision loss*gainL)/
      (10000*(floorEndCoeff κ₁ d₁ Ep precision*gainL))=floorEpsilon κ₁ d₁ Ep precision loss := by
  have hE := floorEndCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  unfold floorEpsilon
  field_simp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign
