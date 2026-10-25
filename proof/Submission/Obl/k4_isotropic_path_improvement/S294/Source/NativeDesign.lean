-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeDesign, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Window
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.QualificationParameters
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalPreStateScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign

open Parent.Qualification.Jets2
open Parent.Qualification.PhysicalModel

noncomputable section

/-- Conditions on the fixed, pre-data source parameters. -/
def Valid (κ₁ d₁ : ℝ) (precision loss : ℝ) : Prop :=
  0 ≤ d₁ ∧ d₁ < 1 ∧ 0 < κ₁ ∧ κ₁ ≤ 1 ∧ 1 ≤ precision ∧ 0 < loss ∧ loss ≤ 1

def clockCoeff (Ep : ℕ) (precision : ℝ) : ℝ :=
  4*(((Ep:ℝ)+1)*precision+3)

def analyticEpsilon (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  loss/(1000000*((Ep:ℝ)+1)*clockCoeff Ep precision)

def alphaBudget (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  nativeQualificationBudget d₁ (qualDegree κ₁) (analyticEpsilon Ep precision loss)

def zetaCoeff (κ₁ d₁ : ℝ) (Ep : ℕ) (precision : ℝ) : ℝ :=
  clockCoeff Ep precision*nativeQualificationDepth d₁ (qualDegree κ₁)+1

/-- The number of residual intervals is fixed before every scale and datum. -/
def residualSteps (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℕ :=
  ⌈64*(zetaCoeff κ₁ d₁ Ep precision+1)/alphaBudget κ₁ d₁ Ep precision loss⌉₊+2

def residualLength (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℕ :=
  residualSteps κ₁ d₁ Ep precision loss+1

/-- One small exponent pays the complete finite residual product. -/
def massCoeff (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  min (loss/((Ep:ℝ)+1)) (alphaBudget κ₁ d₁ Ep precision loss)/
    (100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1)) / max 1 κ₁⁻¹

/-- An additional power pays the physical error and the final displayed row scale. -/
def rhoPower (κ₁ : ℝ) (Ep : ℕ) (precision : ℝ) : ℕ :=
  ⌈100*clockCoeff Ep precision/κ₁⌉₊+4

def rhoCoeff (κ₁ d₁ : ℝ) (Ep : ℕ) (precision : ℝ) : ℝ :=
  (rhoPower κ₁ Ep precision:ℝ)*zetaCoeff κ₁ d₁ Ep precision+1

def regularitySteps (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℕ :=
  ⌈16*(rhoCoeff κ₁ d₁ Ep precision+1)/massCoeff κ₁ d₁ Ep precision loss⌉₊+2

def regularityLength (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℕ :=
  regularitySteps κ₁ d₁ Ep precision loss+1

def regularityCoeff (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  massCoeff κ₁ d₁ Ep precision loss/(400*(regularityLength κ₁ d₁ Ep precision loss:ℝ))

def floorEndCoeff (κ₁ d₁ : ℝ) (Ep : ℕ) (precision : ℝ) : ℝ :=
  rhoCoeff κ₁ d₁ Ep precision+zetaCoeff κ₁ d₁ Ep precision+4

def floorEpsilon (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  regularityCoeff κ₁ d₁ Ep precision loss/(10000*floorEndCoeff κ₁ d₁ Ep precision)

def floorEta (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  originalPreStateEta d₁ (floorEpsilon κ₁ d₁ Ep precision loss)
    (regularityLength κ₁ d₁ Ep precision loss)

def floorStartCoeff (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  regularityCoeff κ₁ d₁ Ep precision loss/1000

def coefficientCoeff (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  min 1 (floorEta κ₁ d₁ Ep precision loss)*regularityCoeff κ₁ d₁ Ep precision loss/100000000

def graphTargetCoeff (κ₁ d₁ : ℝ) (Ep : ℕ) (precision : ℝ) : ℝ :=
  16*floorEndCoeff κ₁ d₁ Ep precision+16*clockCoeff Ep precision/κ₁

def graphLowerCoeff (κ₁ d₁ : ℝ) (Ep : ℕ) (precision : ℝ) : ℝ :=
  1000*(graphTargetCoeff κ₁ d₁ Ep precision+1)/(1-d₁)

def auxiliaryChiCoeff (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  coefficientCoeff κ₁ d₁ Ep precision loss/1000

def auxiliaryFinest (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℕ :=
  ⌈(graphLowerCoeff κ₁ d₁ Ep precision+2*floorEndCoeff κ₁ d₁ Ep precision+1000)/
    auxiliaryChiCoeff κ₁ d₁ Ep precision loss⌉₊+2

/-- The depth pays the original native power range as well as all floor depths. -/
def depth (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  max 1 ((2+(rhoPower κ₁ Ep precision:ℝ)+
    (auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ)+
    |graphLowerCoeff κ₁ d₁ Ep precision|+|floorEndCoeff κ₁ d₁ Ep precision|)^4)

/-- The small front exponent is chosen after the actual P1 floor theorem. -/
def budget (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ := by
  classical
  exact if Valid κ₁ d₁ precision loss then
    min 1 (coefficientCoeff κ₁ d₁ Ep precision loss/(10^20*depth κ₁ d₁ Ep precision loss))
  else 1

theorem clockCoeff_pos {Ep : ℕ} {precision : ℝ} (hprecision : 1 ≤ precision) :
    0 < clockCoeff Ep precision := by
  unfold clockCoeff
  have hp : 0 < precision := zero_lt_one.trans_le hprecision
  positivity

theorem analyticEpsilon_pos {Ep : ℕ} {precision loss : ℝ}
    (hprecision : 1 ≤ precision) (hloss : 0 < loss) :
    0 < analyticEpsilon Ep precision loss := by
  unfold analyticEpsilon
  have := clockCoeff_pos (Ep:=Ep) hprecision
  positivity

theorem alphaBudget_pos (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    0 < alphaBudget κ₁ d₁ Ep precision loss :=
  nativeQualificationBudget_pos _ _ _

theorem zetaCoeff_pos (κ₁ d₁ : ℝ) {Ep : ℕ} {precision : ℝ} (hprecision : 1 ≤ precision) :
    0 < zetaCoeff κ₁ d₁ Ep precision := by
  unfold zetaCoeff
  have := clockCoeff_pos (Ep:=Ep) hprecision
  have := one_le_nativeQualificationDepth d₁ (qualDegree κ₁)
  positivity

theorem massCoeff_pos (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ} (hloss : 0 < loss) :
    0 < massCoeff κ₁ d₁ Ep precision loss := by
  unfold massCoeff
  have := alphaBudget_pos κ₁ d₁ Ep precision loss
  have hmax : (0:ℝ) < max 1 κ₁⁻¹ := zero_lt_one.trans_le (le_max_left _ _)
  positivity

/-- The additional clock factor can only decrease the positive mass budget. -/
theorem massCoeff_le_unscaled (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hloss : 0 < loss) :
    massCoeff κ₁ d₁ Ep precision loss ≤
      min (loss/((Ep:ℝ)+1)) (alphaBudget κ₁ d₁ Ep precision loss)/
        (100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1)) := by
  unfold massCoeff
  apply div_le_self
  · have := alphaBudget_pos κ₁ d₁ Ep precision loss
    positivity
  · exact le_max_left _ _

/-- The Lipschitz power fits the physical clock even for arbitrarily small κ₁. -/
theorem massCoeff_le_kappa {κ₁ : ℝ} (d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hloss1 : loss ≤ 1) :
    massCoeff κ₁ d₁ Ep precision loss ≤ κ₁/100000000 := by
  have hE : (0:ℝ) < (Ep:ℝ)+1 := by positivity
  have hdiv : loss/((Ep:ℝ)+1) ≤ 1 := (div_le_one hE).mpr (by
    have := Nat.cast_nonneg (α:=ℝ) Ep
    linarith)
  have hL : (0:ℝ) ≤ residualLength κ₁ d₁ Ep precision loss := Nat.cast_nonneg _
  have hD : (0:ℝ) < 100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1) := by positivity
  have hbase : min (loss/((Ep:ℝ)+1)) (alphaBudget κ₁ d₁ Ep precision loss)/
      (100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1)) ≤ 1/100000000 := by
    calc
      _ ≤ 1/(100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1)) :=
        div_le_div_of_nonneg_right ((min_le_left _ _).trans hdiv) hD.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have hInv : (1:ℝ) ≤ κ₁⁻¹ := (one_le_inv₀ hκ).mpr hκ1
  unfold massCoeff
  rw [max_eq_right hInv,div_inv_eq_mul]
  convert mul_le_mul_of_nonneg_right hbase hκ.le using 1 <;> ring

theorem rhoCoeff_pos (κ₁ d₁ : ℝ) {Ep : ℕ} {precision : ℝ} (hprecision : 1 ≤ precision) :
    0 < rhoCoeff κ₁ d₁ Ep precision := by
  unfold rhoCoeff
  have := zetaCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  positivity

theorem regularityLength_pos (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    0 < regularityLength κ₁ d₁ Ep precision loss := by
  unfold regularityLength
  omega

theorem regularityCoeff_pos (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ} (hloss : 0 < loss) :
    0 < regularityCoeff κ₁ d₁ Ep precision loss := by
  unfold regularityCoeff
  have := massCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hc : (0:ℝ) < regularityLength κ₁ d₁ Ep precision loss :=
    Nat.cast_pos.mpr (regularityLength_pos _ _ _ _ _)
  positivity

theorem floorEndCoeff_pos (κ₁ d₁ : ℝ) {Ep : ℕ} {precision : ℝ} (hprecision : 1 ≤ precision) :
    0 < floorEndCoeff κ₁ d₁ Ep precision := by
  unfold floorEndCoeff
  have := rhoCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  have := zetaCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  positivity

theorem floorEpsilon_pos (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hprecision : 1 ≤ precision) (hloss : 0 < loss) :
    0 < floorEpsilon κ₁ d₁ Ep precision loss := by
  unfold floorEpsilon
  have := regularityCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have := floorEndCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  positivity

theorem coefficientCoeff_pos (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ} (hloss : 0 < loss) :
    0 < coefficientCoeff κ₁ d₁ Ep precision loss := by
  unfold coefficientCoeff floorEta
  have := regularityCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have := originalPreStateEta_pos d₁ (floorEpsilon κ₁ d₁ Ep precision loss)
    (regularityLength κ₁ d₁ Ep precision loss)
  positivity

theorem one_le_depth (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    1 ≤ depth κ₁ d₁ Ep precision loss := le_max_left _ _

theorem budget_pos (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    0 < budget κ₁ d₁ Ep precision loss := by
  unfold budget
  split_ifs with h
  · have hloss : 0 < loss := h.2.2.2.2.2.1
    have := coefficientCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
    have := one_le_depth κ₁ d₁ Ep precision loss
    positivity
  · exact zero_lt_one

theorem budget_le_one (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    budget κ₁ d₁ Ep precision loss ≤ 1 := by
  unfold budget
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign
