-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeGridProfile, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesignPowers
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootGridExistence

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign

open Parent.Qualification.Jets2
open Parent.Qualification.PhysicalModel

noncomputable section

theorem massCoeff_le_one (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ} (hloss1 : loss ≤ 1) :
    massCoeff κ₁ d₁ Ep precision loss ≤ 1 := by
  have hE : (0:ℝ) < (Ep:ℝ)+1 := by positivity
  have hdiv : loss/((Ep:ℝ)+1) ≤ 1 := (div_le_one hE).mpr (by have := Nat.cast_nonneg (α:=ℝ) Ep; linarith)
  have hL : (0:ℝ) ≤ residualLength κ₁ d₁ Ep precision loss := Nat.cast_nonneg _
  unfold massCoeff
  apply (div_le_one (zero_lt_one.trans_le (le_max_left 1 κ₁⁻¹))).mpr
  apply le_trans _ (le_max_left 1 κ₁⁻¹)
  apply (div_le_one (by positivity : 0 < 100000000*((residualLength κ₁ d₁ Ep precision loss:ℝ)+1))).mpr
  exact ((min_le_left _ _).trans hdiv).trans (by nlinarith)

theorem regularityCoeff_le_one (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hloss1 : loss ≤ 1) :
    regularityCoeff κ₁ d₁ Ep precision loss ≤ 1 := by
  have hn : (1:ℝ) ≤ regularityLength κ₁ d₁ Ep precision loss := by
    exact_mod_cast (regularityLength_pos κ₁ d₁ Ep precision loss)
  unfold regularityCoeff
  exact (div_le_one (by positivity : 0 < 400*(regularityLength κ₁ d₁ Ep precision loss:ℝ))).mpr
    ((massCoeff_le_one κ₁ d₁ hloss1).trans (by nlinarith))

theorem floorStartCoeff_lt_one (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hloss1 : loss ≤ 1) :
    floorStartCoeff κ₁ d₁ Ep precision loss < 1 := by
  have hh := regularityCoeff_le_one κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss1
  unfold floorStartCoeff
  linarith

/-- The concrete pre-data design meets every scalar requirement of
the uniform actual original-grid factory. -/
def nativeGridProfile {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss gainL : ℝ}
    (hv : Valid κ₁ d₁ precision loss) (hg : 0 < gainL) : OriginalRootGridPowers := by
  have hprecision := hv.2.2.2.2.1
  have hloss := hv.2.2.2.2.2.1
  have hloss1 := hv.2.2.2.2.2.2
  have hκ := hv.2.2.1
  have hC : 1 ≤ clockCoeff Ep precision := by
    have hh : (1:ℝ) ≤ ((Ep:ℝ)+1)*precision :=
      one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α:=ℝ) Ep; linarith) hprecision
    unfold clockCoeff
    linarith
  have hD : 1 ≤ nativeQualificationDepth d₁ (qualDegree κ₁) := one_le_nativeQualificationDepth _ _
  have hP : 1 ≤ rhoPower κ₁ Ep precision := by unfold rhoPower; omega
  have hPcast : (1:ℝ) ≤ rhoPower κ₁ Ep precision := by exact_mod_cast hP
  have hs := floorStartCoeff_lt_one κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss1
  have hsD : floorStartCoeff κ₁ d₁ Ep precision loss < 
      (rhoPower κ₁ Ep precision:ℝ)*nativeQualificationDepth d₁ (qualDegree κ₁) :=
    hs.trans_le (one_le_mul_of_one_le_of_one_le hPcast hD)
  have hRho := rhoCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  have hZeta := zetaCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  have hGraph : rhoCoeff κ₁ d₁ Ep precision+zetaCoeff κ₁ d₁ Ep precision+1 < 
      graphTargetCoeff κ₁ d₁ Ep precision := by
    have hh : 0 ≤ 16*clockCoeff Ep precision/κ₁ := by
      exact div_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hC)) hκ.le
    unfold graphTargetCoeff floorEndCoeff
    linarith
  refine {
    lower := gainL
    upper := clockCoeff Ep precision*gainL
    D := nativeQualificationDepth d₁ (qualDegree κ₁)
    margin := gainL
    lower_pos := hg
    upper_lower := by nlinarith
    D_one := hD
    margin_pos := hg
    rhoPower := rhoPower κ₁ Ep precision
    rhoPower_one := hP
    regIntervals := regularitySteps κ₁ d₁ Ep precision loss
    resIntervals := residualSteps κ₁ d₁ Ep precision loss
    regIntervals_pos := by unfold regularitySteps; omega
    resIntervals_pos := residualSteps_pos _ _ _ _ _
    regRatio := massCoeff κ₁ d₁ Ep precision loss*gainL/4
    resRatio := alphaBudget κ₁ d₁ Ep precision loss*gainL/8
    regRatio_pos := by have := massCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss; positivity
    resRatio_pos := by have := alphaBudget_pos κ₁ d₁ Ep precision loss; positivity
    regRoom := ?_
    resRoom := ?_
    start := floorStartCoeff κ₁ d₁ Ep precision loss*gainL
    target := graphTargetCoeff κ₁ d₁ Ep precision*gainL
    count := coefficientCoeff κ₁ d₁ Ep precision loss*gainL
    start_pos := by
      unfold floorStartCoeff
      have := regularityCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
      positivity
    startRoom := ?_
    targetRoom := ?_
    count_pos := mul_pos (coefficientCoeff_pos κ₁ d₁ hloss) hg
  }
  · have hh := mul_lt_mul_of_pos_right (regularity_ratio_room κ₁ d₁
      (Ep:=Ep) hprecision hloss) hg
    convert hh using 1 <;> (try simp only [rhoCoeff,zetaCoeff]) <;> ring
  · have hh := mul_lt_mul_of_pos_right (residual_ratio_room κ₁ d₁
      (Ep:=Ep) (loss:=loss) hprecision) hg
    convert hh using 1 <;> (try simp only [zetaCoeff]) <;> ring
  · have hh := mul_lt_mul_of_pos_right hsD hg
    nlinarith
  · have hh := mul_lt_mul_of_pos_right hGraph hg
    convert hh using 1 <;> (try simp only [rhoCoeff,zetaCoeff]) <;> ring

theorem nativeGridProfile_zetaExponent {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss gainL : ℝ}
    (hv : Valid κ₁ d₁ precision loss) (hg : 0 < gainL) :
    (nativeGridProfile (Ep:=Ep) hv hg).zetaExponent=zetaCoeff κ₁ d₁ Ep precision*gainL := by
  change (clockCoeff Ep precision*gainL)*nativeQualificationDepth d₁ (qualDegree κ₁)+gainL=_
  unfold zetaCoeff
  ring

theorem nativeGridProfile_rhoExponent {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss gainL : ℝ}
    (hv : Valid κ₁ d₁ precision loss) (hg : 0 < gainL) :
    (nativeGridProfile (Ep:=Ep) hv hg).rhoExponent=rhoCoeff κ₁ d₁ Ep precision*gainL := by
  unfold OriginalRootGridPowers.rhoExponent
  rw [nativeGridProfile_zetaExponent hv hg]
  change (rhoPower κ₁ Ep precision:ℝ)*(zetaCoeff κ₁ d₁ Ep precision*gainL)+gainL=_
  unfold rhoCoeff
  ring

theorem nativeGridProfile_floorExponent_le {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss gainL : ℝ}
    (hv : Valid κ₁ d₁ precision loss) (hg : 0 < gainL) :
    (nativeGridProfile (Ep:=Ep) hv hg).floorExponent ≤ floorEndCoeff κ₁ d₁ Ep precision*gainL := by
  unfold OriginalRootGridPowers.floorExponent
  rw [nativeGridProfile_rhoExponent hv hg,nativeGridProfile_zetaExponent hv hg]
  change rhoCoeff κ₁ d₁ Ep precision*gainL+zetaCoeff κ₁ d₁ Ep precision*gainL+gainL ≤ _
  unfold floorEndCoeff
  nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign
