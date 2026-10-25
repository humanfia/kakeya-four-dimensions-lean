-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeDesignPowers, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign

open Parent.Qualification.Jets2

noncomputable section

theorem residualSteps_pos (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    0 < residualSteps κ₁ d₁ Ep precision loss := by
  unfold residualSteps
  omega

theorem residual_ratio_room (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hprecision : 1 ≤ precision) :
    zetaCoeff κ₁ d₁ Ep precision <
      (alphaBudget κ₁ d₁ Ep precision loss/8)*(residualSteps κ₁ d₁ Ep precision loss:ℝ) := by
  have ha := alphaBudget_pos κ₁ d₁ Ep precision loss
  have hz := zetaCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  have hc := Nat.le_ceil (64*(zetaCoeff κ₁ d₁ Ep precision+1)/alphaBudget κ₁ d₁ Ep precision loss)
  have hh : 64*(zetaCoeff κ₁ d₁ Ep precision+1)/alphaBudget κ₁ d₁ Ep precision loss ≤
      (residualSteps κ₁ d₁ Ep precision loss:ℝ) := by
    unfold residualSteps
    push_cast
    linarith
  have hm := (div_le_iff₀ ha).mp hh
  nlinarith

theorem native_mass_room (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ} (hloss : 0 < loss) :
    (200*(residualLength κ₁ d₁ Ep precision loss:ℝ)+100)*massCoeff κ₁ d₁ Ep precision loss ≤
      alphaBudget κ₁ d₁ Ep precision loss := by
  have hm := massCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hc : (0:ℝ) ≤ residualLength κ₁ d₁ Ep precision loss := Nat.cast_nonneg _
  have he : (100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1))*
      massCoeff κ₁ d₁ Ep precision loss ≤
      min (loss/((Ep:ℝ)+1)) (alphaBudget κ₁ d₁ Ep precision loss) := by
    calc
      _ ≤ (100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1))*
          (min (loss/((Ep:ℝ)+1)) (alphaBudget κ₁ d₁ Ep precision loss)/
            (100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1))) :=
        mul_le_mul_of_nonneg_left (massCoeff_le_unscaled κ₁ d₁ hloss) (by positivity)
      _ = _ := by field_simp
  have hi := min_le_right (loss/((Ep:ℝ)+1)) (alphaBudget κ₁ d₁ Ep precision loss)
  nlinarith

theorem regularity_ratio_room (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hprecision : 1 ≤ precision) (hloss : 0 < loss) :
    rhoCoeff κ₁ d₁ Ep precision <
      (massCoeff κ₁ d₁ Ep precision loss/4)*(regularitySteps κ₁ d₁ Ep precision loss:ℝ) := by
  have hm := massCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hr := rhoCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  have hc := Nat.le_ceil (16*(rhoCoeff κ₁ d₁ Ep precision+1)/massCoeff κ₁ d₁ Ep precision loss)
  have hh : 16*(rhoCoeff κ₁ d₁ Ep precision+1)/massCoeff κ₁ d₁ Ep precision loss ≤
      (regularitySteps κ₁ d₁ Ep precision loss:ℝ) := by
    unfold regularitySteps
    push_cast
    linarith
  have hi := (div_le_iff₀ hm).mp hh
  nlinarith

theorem coefficient_le_regularity (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ} (hloss : 0 < loss) :
    coefficientCoeff κ₁ d₁ Ep precision loss ≤ regularityCoeff κ₁ d₁ Ep precision loss/100000000 := by
  have hr := regularityCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  unfold coefficientCoeff
  exact div_le_div_of_nonneg_right
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (min_le_left 1 (floorEta κ₁ d₁ Ep precision loss)) hr.le)
    (by norm_num)

theorem coefficient_floor_room (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ} (hloss : 0 < loss) :
    100000*coefficientCoeff κ₁ d₁ Ep precision loss ≤
      floorEta κ₁ d₁ Ep precision loss*floorStartCoeff κ₁ d₁ Ep precision loss := by
  have hr := regularityCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  calc
    _ = min 1 (floorEta κ₁ d₁ Ep precision loss)*floorStartCoeff κ₁ d₁ Ep precision loss := by
      unfold coefficientCoeff floorStartCoeff
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (min_le_right _ _) (div_nonneg hr.le (by norm_num))

theorem auxiliaryChiCoeff_pos (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ} (hloss : 0 < loss) :
    0 < auxiliaryChiCoeff κ₁ d₁ Ep precision loss := by
  unfold auxiliaryChiCoeff
  exact div_pos (coefficientCoeff_pos κ₁ d₁ hloss) (by norm_num)

theorem auxiliaryFinest_ge_two (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    2 ≤ auxiliaryFinest κ₁ d₁ Ep precision loss := by
  unfold auxiliaryFinest
  omega

theorem auxiliary_finest_covers_graph (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hloss : 0 < loss) :
    graphLowerCoeff κ₁ d₁ Ep precision+2*floorEndCoeff κ₁ d₁ Ep precision+1000 ≤
      auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ) := by
  have hχ := auxiliaryChiCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  rw [mul_comm (auxiliaryChiCoeff κ₁ d₁ Ep precision loss)]
  apply (div_le_iff₀ hχ).mp
  have hc := Nat.le_ceil ((graphLowerCoeff κ₁ d₁ Ep precision+2*floorEndCoeff κ₁ d₁ Ep precision+1000)/
    auxiliaryChiCoeff κ₁ d₁ Ep precision loss)
  unfold auxiliaryFinest
  push_cast
  linarith

theorem auxiliary_coarse_below_floor_start (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hloss : 0 < loss) :
    auxiliaryChiCoeff κ₁ d₁ Ep precision loss/(auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ) ≤
      floorStartCoeff κ₁ d₁ Ep precision loss := by
  have hχ := auxiliaryChiCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hn : (1:ℝ) ≤ auxiliaryFinest κ₁ d₁ Ep precision loss := by
    exact_mod_cast (le_trans (by omega : 1≤2) (auxiliaryFinest_ge_two κ₁ d₁ Ep precision loss))
  have hc := coefficient_le_regularity κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hr := regularityCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  calc
    _ ≤ auxiliaryChiCoeff κ₁ d₁ Ep precision loss := div_le_self hχ.le hn
    _ ≤ _ := by unfold auxiliaryChiCoeff floorStartCoeff; linarith

/-- The front's scalar powers fit far inside the native primitive budget. -/
theorem front_budget_room {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss : ℝ}
    (hvalid : Valid κ₁ d₁ precision loss) :
    1000000*budget κ₁ d₁ Ep precision loss ≤ coefficientCoeff κ₁ d₁ Ep precision loss := by
  have hc := coefficientCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hvalid.2.2.2.2.2.1
  have hd := one_le_depth κ₁ d₁ Ep precision loss
  have hb := budget_pos κ₁ d₁ Ep precision loss
  have hbound : budget κ₁ d₁ Ep precision loss ≤
      coefficientCoeff κ₁ d₁ Ep precision loss/(10^20*depth κ₁ d₁ Ep precision loss) := by
    unfold budget
    rw [ite_eq_left hvalid]
    exact min_le_right _ _
  have hh := (le_div_iff₀ (by positivity : 0 < (10:ℝ)^20*depth κ₁ d₁ Ep precision loss)).mp hbound
  norm_num at hh
  nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign
