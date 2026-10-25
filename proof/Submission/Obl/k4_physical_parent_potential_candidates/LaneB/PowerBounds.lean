import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.BallCertificate

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set

noncomputable section

namespace MeasureNorming

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

def conicPower (J : ℕ) : ℕ := 4*J+20

def detPower (J Dc : ℕ) : ℕ := 4*Dc*conicPower J

def radiusPower (J Dc : ℕ) : ℕ := detPower J Dc+20

def conditioningPower (J Dc : ℕ) : ℕ := 6*radiusPower J Dc+detPower J Dc+3

def denominatorPower (J Dc : ℕ) : ℕ := 4*conditioningPower J Dc+11

def framePower (J Dc : ℕ) : ℕ := 5*denominatorPower J Dc+7

def restorationPower (J Dc : ℕ) : ℕ :=
  100*(framePower J Dc+denominatorPower J Dc+J+radiusPower J Dc+conicPower J+1)

def powerRadius (A : ℝ) (J Dc : ℕ) : ℝ := (A^radiusPower J Dc)⁻¹

def powerDet (A : ℝ) (J Dc : ℕ) : ℝ := (A^detPower J Dc)⁻¹

attribute [local irreducible] conicPower detPower radiusPower conditioningPower
  denominatorPower framePower restorationPower

private theorem const_power {A : ℝ} (hA : 2 ≤ A) (n : ℕ) {b : ℝ} (hb : b ≤ 2^n) : b ≤ A^n :=
  hb.trans (pow_le_pow_left₀ (by norm_num) hA n)

structure PatchPowerBounds (A : ℝ) (J Dc : ℕ) : Prop where
  radius_pos : 0 < powerRadius A J Dc
  radius_le_one : powerRadius A J Dc ≤ 1
  det_pos : 0 < powerDet A J Dc
  radius_small : 4*powerRadius A J Dc ≤ 1/2
  det_stable : 1152*A^3*powerRadius A J Dc ≤ powerDet A J Dc/2
  conic_mono : A ≤ A^conicPower J
  conic_floor : ((A^conicPower J)^4)⁻¹ ≤ (100*(2*A)^J)⁻¹
  conic_upper : 9*A ≤ (A^conicPower J)^4
  conic_error : (A^conicPower J)^(4*Dc+1) ≤ A^restorationPower J Dc
  determinant_eq : ((A^conicPower J)^(4*Dc))⁻¹ = powerDet A J Dc
  coefficient : 95904*(patchFrame A (powerRadius A J Dc) (powerDet A J Dc))^4*
    ((powerRadius A J Dc)⁻¹)^2 ≤ A^restorationPower J Dc
  mass : 2*A^(3*(radiusPower J Dc+1)+14) ≤ A^restorationPower J Dc
  smallness : 18000000*(patchFrame A (powerRadius A J Dc) (powerDet A J Dc))^9*
    (2000*(patchBudget A (powerRadius A J Dc) (powerDet A J Dc))^4)^5*A^(2*J) ≤
      A^restorationPower J Dc
  value : patchError A (powerRadius A J Dc) (powerDet A J Dc)*A^(2*J) ≤
    A^restorationPower J Dc
  vertical_value : 4*(patchFrame A (powerRadius A J Dc) (powerDet A J Dc))^2 ≤
    A^restorationPower J Dc
  tube : 4*(patchFrame A (powerRadius A J Dc) (powerDet A J Dc))^3 ≤
    A^restorationPower J Dc
  lower_derivative : 2*patchFrame A (powerRadius A J Dc) (powerDet A J Dc) ≤
    A^restorationPower J Dc
  upper_derivative : 4*patchFrame A (powerRadius A J Dc) (powerDet A J Dc) ≤
    A^restorationPower J Dc
  curvature : 2*(patchFrame A (powerRadius A J Dc) (powerDet A J Dc))^2 ≤
    A^restorationPower J Dc

/-- Every radius, conditioning, and accuracy loss in the local analytic
restoration is a fixed power of one parameter. -/
theorem patch_power_bounds {A : ℝ} (hA : 2 ≤ A) (J Dc : ℕ) : PatchPowerBounds A J Dc := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  let P := conicPower J
  let N := detPower J Dc
  let M := radiusPower J Dc
  let B := conditioningPower J Dc
  let U := denominatorPower J Dc
  let V := framePower J Dc
  let C := restorationPower J Dc
  let r := powerRadius A J Dc
  let ν := powerDet A J Dc
  have hP : 1 ≤ P := by simp only [P, conicPower]; omega
  have hM : 20 ≤ M := by simp only [M, radiusPower]; omega
  have hNrel : M = N+20 := by simp only [M, N, radiusPower]
  have hr : 0 < r := inv_pos.mpr (pow_pos hA0 _)
  have hν : 0 < ν := inv_pos.mpr (pow_pos hA0 _)
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hA1)
  have hconstant8 : (8:ℝ) ≤ A^M := by
    exact (const_power hA 3 (by norm_num : (8:ℝ) ≤ 2^3)).trans (pow_le_pow_right₀ hA1 (by omega))
  have hsmallr : 4*r ≤ 1/2 := by
    dsimp only [r, powerRadius]
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
    have hh : (8:ℝ)/A^M ≤ 1 := (div_le_one (pow_pos hA0 M)).mpr hconstant8
    convert hh using 1 <;> ring
  have hstable : 1152*A^3*r ≤ ν/2 := by
    have h2304 : (2304:ℝ) ≤ A^17 :=
      (const_power hA 12 (by norm_num : (2304:ℝ) ≤ 2^12)).trans
        (pow_le_pow_right₀ hA1 (by decide : 12 ≤ 17))
    have he : (A^M) = A^N*A^20 := by rw [hNrel, pow_add]
    have hmul : (2304:ℝ)*A^3 ≤ A^20 := by
      calc
        _ ≤ A^17*A^3 := mul_le_mul_of_nonneg_right h2304 (by positivity)
        _ = _ := by ring
    dsimp only [r, ν, powerRadius, powerDet]
    rw [show radiusPower J Dc = M from rfl, show detPower J Dc = N from rfl, he]
    field_simp
    nlinarith
  have hRmono : A ≤ A^P := by simpa using pow_le_pow_right₀ hA1 hP
  have h2A : 2*A ≤ A^2 := by nlinarith
  have hdense : (2*A)^J ≤ A^(2*J) := by
    convert pow_le_pow_left₀ (by positivity : 0 ≤ 2*A) h2A J using 1 <;> ring
  have hfloorDen : 100*(2*A)^J ≤ (A^P)^4 := by
    calc
      _ ≤ A^7*A^(2*J) := mul_le_mul (const_power hA 7 (by norm_num)) hdense
        (by positivity) (by positivity)
      _ = A^(2*J+7) := by rw [pow_add]; ring
      _ ≤ A^(P*4) := pow_le_pow_right₀ hA1 (by simp only [P, conicPower]; omega)
      _ = (A^P)^4 := pow_mul _ _ _
  have hupper : 9*A ≤ (A^P)^4 := by
    calc
      _ ≤ A^4*A := mul_le_mul_of_nonneg_right (const_power hA 4 (by norm_num)) hA0.le
      _ = A^5 := by ring
      _ ≤ A^(P*4) := pow_le_pow_right₀ hA1 (by simp only [P, conicPower]; omega)
      _ = _ := pow_mul _ _ _
  have hdivision : 2/(r^6*ν) = 2*A^(6*M+N) := by
    dsimp only [r, ν, powerRadius, powerDet]
    change 2/((A^M)⁻¹^6*(A^N)⁻¹) = _
    rw [show 6*M+N = M*6+N by omega, pow_add, pow_mul]
    simp only [inv_pow, mul_inv, inv_inv, div_eq_mul_inv]
  have hB : patchBudget A r ν ≤ A^B := by
    have hS1 : 1 ≤ 6*M+N := by omega
    have hS : A ≤ A^(6*M+N) := by simpa using pow_le_pow_right₀ hA1 hS1
    have hS0 : 1 ≤ A^(6*M+N) := one_le_pow₀ hA1
    calc
      _ = 2+A+2*A^(6*M+N) := by rw [patchBudget, hdivision]
      _ ≤ 5*A^(6*M+N) := by linarith
      _ ≤ A^3*A^(6*M+N) := mul_le_mul_of_nonneg_right (const_power hA 3 (by norm_num)) (by positivity)
      _ = A^B := by simp only [B, conditioningPower, M, N]; rw [← pow_add]; congr 1; omega
  have hBudget0 : 0 ≤ patchBudget A r ν := by simp only [patchBudget]; positivity
  have hU : 2000*(patchBudget A r ν)^4 ≤ A^U := by
    calc
      _ ≤ A^11*(A^B)^4 := mul_le_mul (const_power hA 11 (by norm_num))
        (pow_le_pow_left₀ hBudget0 hB 4) (by positivity) (by positivity)
      _ = _ := by simp only [U, denominatorPower, B]; rw [← pow_mul, ← pow_add]; congr 1; omega
  have hV : patchFrame A r ν ≤ A^V := by
    change 100*(2000*(patchBudget A r ν)^4)^5 ≤ _
    calc
      _ ≤ A^7*(A^U)^5 := mul_le_mul (const_power hA 7 (by norm_num))
        (pow_le_pow_left₀ (by positivity) hU 5) (by positivity) (by positivity)
      _ = _ := by simp only [V, framePower, U]; rw [← pow_mul, ← pow_add]; congr 1; omega
  have hF0 : 0 ≤ patchFrame A r ν := (zero_le_one.trans (patchFrame_one_le hA1 hr hν))
  have hmono (n : ℕ) (hn : n ≤ C) : A^n ≤ A^C := pow_le_pow_right₀ hA1 hn
  have hsmall : 18000000*(patchFrame A r ν)^9*(2000*(patchBudget A r ν)^4)^5*A^(2*J) ≤ A^C := by
    calc
      _ ≤ A^25*(A^V)^9*(A^U)^5*A^(2*J) := by
        gcongr
        · exact const_power hA 25 (by norm_num)
      _ = A^(25+9*V+5*U+2*J) := by simp only [pow_mul, pow_add]; ring
      _ ≤ _ := hmono _ (by simp only [C, restorationPower, V, U, M, P]; omega)
  have hvalue : patchError A r ν*A^(2*J) ≤ A^C := by
    apply le_trans ?_ hsmall
    dsimp only [patchError]
    have hp := pow_le_pow_right₀ (patchFrame_one_le hA1 hr hν) (by decide : 8 ≤ 9)
    gcongr
  have hcoeff : 95904*(patchFrame A r ν)^4*(r⁻¹)^2 ≤ A^C := by
    calc
      _ ≤ A^17*(A^V)^4*(A^M)^2 := by
        dsimp only [r, powerRadius]
        simp only [inv_inv]
        gcongr
        · exact const_power hA 17 (by norm_num)
        · simpa only [r, powerRadius] using hV
      _ = A^(17+4*V+2*M) := by simp only [pow_mul, pow_add]; ring
      _ ≤ _ := hmono _ (by simp only [C, restorationPower, V, U, M, P]; omega)
  have hmass : 2*A^(3*(M+1)+14) ≤ A^C := by
    calc
      _ ≤ A*A^(3*(M+1)+14) := mul_le_mul_of_nonneg_right hA (by positivity)
      _ = A^(3*M+18) := (pow_succ' A (3*(M+1)+14)).symm.trans
        (congrArg (fun n : ℕ => A^n) (by omega : (3*(M+1)+14)+1 = 3*M+18))
      _ ≤ _ := hmono _ (by simp only [C, restorationPower, V, U, M, P]; omega)
  have hsimple (a n : ℕ) (ha : (a:ℝ) ≤ A^2) (hn : n ≤ 3) :
      (a:ℝ)*(patchFrame A r ν)^n ≤ A^C := by
    calc
      _ ≤ A^2*(A^V)^3 := mul_le_mul ha
        ((pow_le_pow_right₀ (patchFrame_one_le hA1 hr hν) hn).trans
          (pow_le_pow_left₀ hF0 hV 3)) (by positivity) (by positivity)
      _ = A^(2+3*V) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ ≤ _ := hmono _ (by simp only [C, restorationPower, V, U, M, P]; omega)
  refine {
    radius_pos := hr
    radius_le_one := hr1
    det_pos := hν
    radius_small := hsmallr
    det_stable := hstable
    conic_mono := hRmono
    conic_floor := ?_
    conic_upper := hupper
    conic_error := ?_
    determinant_eq := ?_
    coefficient := hcoeff
    mass := hmass
    smallness := hsmall
    value := hvalue
    vertical_value := hsimple 4 2 (const_power hA 2 (by norm_num)) (by decide)
    tube := hsimple 4 3 (const_power hA 2 (by norm_num)) (by decide)
    lower_derivative := by simpa only [pow_one, Nat.cast_ofNat] using hsimple 2 1 (const_power hA 2 (by norm_num)) (by decide)
    upper_derivative := by simpa only [pow_one, Nat.cast_ofNat] using hsimple 4 1 (const_power hA 2 (by norm_num)) (by decide)
    curvature := hsimple 2 2 (const_power hA 2 (by norm_num)) (by decide) }
  · simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 100*(2*A)^J) hfloorDen
  · rw [← pow_mul]
    have he : P*(4*Dc+1) = N+P := by simp only [P, N, detPower]; ring
    rw [he]
    exact hmono _ (by simp only [C, restorationPower, N, V, U, M, P, radiusPower]; omega)
  · change ((A^P)^(4*Dc))⁻¹ = (A^N)⁻¹
    have he : P*(4*Dc) = N := by simp only [P, N, detPower]; ring
    rw [← pow_mul, he]

end MeasureNorming

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
