-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeQualificationPowerBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.QualScalars

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- The native qualification residual fits half the displayed
accuracy at the literal polynomial coefficient bound. -/
theorem native_qualification_residual_power_budget
    {N h thetaFloor theta graphError etaFit remainder : ℝ}
    (hN : 1 ≤ N) (_hh : 0 < h) (hlarge : 100 ≤ N^h)
    (hfloor : 4*h ≤ thetaFloor) (htheta : N^(-thetaFloor) ≤ theta)
    (hgraph : graphError ≤ N^(-2*thetaFloor))
    (heta : etaFit ≤ N^(-2*thetaFloor)) (hrem : remainder ≤ N^(-2*thetaFloor)) :
    graphError+(1+2*N^h)*(etaFit+remainder) ≤ theta/2 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hH1 : 1 ≤ N^h := by linarith only [hlarge]
  have h14 : (14:ℝ) ≤ (N^h)^3 := by
    have hh' : (3:ℝ) ≤ N^h := by linarith only [hlarge]
    exact (by norm_num : (14:ℝ) ≤ 3^3).trans (pow_le_pow_left₀ (by norm_num) hh' 3)
  have hpower : 14*N^h ≤ N^thetaFloor := by
    calc
      _ ≤ (N^h)^3*N^h := mul_le_mul_of_nonneg_right h14 (Real.rpow_nonneg hNp.le _)
      _ = (N^h)^4 := by ring
      _ = N^(4*h) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hfloor
  calc
    _ ≤ N^(-2*thetaFloor)+(1+2*N^h)*(N^(-2*thetaFloor)+N^(-2*thetaFloor)) := by gcongr
    _ = (3+4*N^h)*N^(-2*thetaFloor) := by ring
    _ ≤ (7*N^h)*N^(-2*thetaFloor) :=
      mul_le_mul_of_nonneg_right (by linarith only [hH1]) (Real.rpow_nonneg hNp.le _)
    _ ≤ (N^thetaFloor/2)*N^(-2*thetaFloor) :=
      mul_le_mul_of_nonneg_right (by linarith only [hpower]) (Real.rpow_nonneg hNp.le _)
    _ = N^(-thetaFloor)/2 := by
      rw [div_mul_eq_mul_div,←Real.rpow_add hNp]
      congr 2
      ring
    _ ≤ _ := div_le_div_of_nonneg_right htheta (by norm_num)

/-- The exact coefficient display cost is polynomial. The fixed
native degree constant is absorbed before the sample. -/
theorem native_qualification_coefficient_power_budget
    (M : ℕ) {N h analyticPower nativePower theta : ℝ}
    (hN : 1 ≤ N) (_hh : 0 < h) (hanalytic0 : 0 ≤ analyticPower)
    (hlarge : max 100 (100*Parent.QualificationClock.coefficientCost M) ≤ N^h)
    (htheta : theta ≤ N^h) (hnative : N^nativePower ≤ N^analyticPower) :
    Parent.QualificationClock.coefficientCost M*
      (3*N^h+(1+2*N^h)*N^nativePower+3*(theta/(8*((M:ℝ)+1)))) ≤ N^(2*h+analyticPower) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hH100 : 100 ≤ N^h := (le_max_left _ _).trans hlarge
  have hH1 : 1 ≤ N^h := by linarith only [hH100]
  have hH0 : 0 ≤ N^h := zero_le_one.trans hH1
  have hcost0 := (Parent.QualificationClock.coefficientCost_pos M).le
  have hcost : 100*Parent.QualificationClock.coefficientCost M ≤ N^h := (le_max_right _ _).trans hlarge
  have hcost9 : 9*Parent.QualificationClock.coefficientCost M ≤ N^h := by linarith only [hcost,hcost0]
  have hNanalytic : 1 ≤ N^analyticPower := Real.one_le_rpow hN hanalytic0
  have hproduct : 1 ≤ N^h*N^analyticPower := one_le_mul_of_one_le_of_one_le hH1 hNanalytic
  have hq : theta/(8*((M:ℝ)+1)) ≤ N^h := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 8*((M:ℝ)+1))]
    have hdenom : (1:ℝ) ≤ 8*((M:ℝ)+1) := by
      have hh' : 0 ≤ (M:ℝ) := Nat.cast_nonneg _
      linarith only [hh']
    exact htheta.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hdenom hH0)
  have hA : 3*N^h ≤ 3*(N^h*N^analyticPower) := by
    have hh' := mul_le_mul_of_nonneg_left hNanalytic hH0
    nlinarith only [hh']
  have hB : (1+2*N^h)*N^nativePower ≤ 3*(N^h*N^analyticPower) := by
    calc
      _ ≤ (3*N^h)*N^analyticPower := by gcongr; linarith only [hH1]
      _ = _ := by ring
  have hQ : theta/(8*((M:ℝ)+1)) ≤ N^h*N^analyticPower := hq.trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hNanalytic hH0)
  have hsum : 3*N^h+(1+2*N^h)*N^nativePower+3*(theta/(8*((M:ℝ)+1))) ≤
      9*(N^h*N^analyticPower) := by linarith only [hA,hB,hQ]
  calc
    _ ≤ Parent.QualificationClock.coefficientCost M*(9*(N^h*N^analyticPower)) :=
      mul_le_mul_of_nonneg_left hsum hcost0
    _ = (9*Parent.QualificationClock.coefficientCost M)*N^h*N^analyticPower := by ring
    _ ≤ N^h*N^h*N^analyticPower :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcost9 hH0)
        (Real.rpow_nonneg hNp.le _)
    _ = _ := by rw [←Real.rpow_add hNp,←Real.rpow_add hNp]; congr 1; ring

/-- All exact qualification display fields at polynomial native
budgets, with the actual mesh and Int coefficient ceiling. -/
theorem native_qualification_display_power_budgets
    (M : ℕ) {N h thetaFloor analyticPower display ch aE theta lam graphError etaFit : ℝ}
    (hN : 1 < N) (hh : 0 < h) (hanalytic0 : 0 ≤ analyticPower)
    (hfloor : 4*h ≤ thetaFloor) (hdisplay : 2*h+analyticPower ≤ display)
    (hlam : 0 < lam) (htheta : N^(-thetaFloor) ≤ theta) (hthetaH : theta ≤ N^h)
    (hgraph : graphError ≤ N^(-2*thetaFloor)) (heta : etaFit ≤ N^(-2*thetaFloor))
    (hrem : lam^((M:ℝ)+1/8) ≤ N^(-2*thetaFloor))
    (hnative : N^(ch*aE) ≤ N^analyticPower)
    (hlarge : max 100 (100*Parent.QualificationClock.coefficientCost M) ≤ N^h) :
    let qmesh := theta/(8*((M:ℝ)+1))
    let qbound : ℤ := ⌈(3*N^h+(1+2*N^h)*N^(ch*aE))/qmesh⌉+2
    0 < qmesh ∧ 0 ≤ qbound ∧
      3*N^h+(1+2*N^h)*N^(ch*aE) ≤ qmesh*((qbound:ℝ)-1) ∧
      graphError+(1+2*N^h)*(etaFit+lam^((M:ℝ)+1/8))+((M:ℝ)+1)*qmesh ≤ theta ∧
      Parent.QualificationClock.coefficientCost M*(qmesh*(qbound:ℝ)) ≤ N^display ∧
      1/N^display ≤ (lam*N^(-(ch*aE)))/lam := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hH100 : 100 ≤ N^h := (le_max_left _ _).trans hlarge
  have hH1 : 1 ≤ N^h := by linarith only [hH100]
  have htheta0 : 0 < theta := (Real.rpow_pos_of_pos hNp _).trans_le htheta
  have hres := native_qualification_residual_power_budget hN.le hh hH100 hfloor htheta hgraph heta hrem
  have hcost := (native_qualification_coefficient_power_budget M hN.le hh hanalytic0 hlarge
    hthetaH hnative).trans (Real.rpow_le_rpow_of_exponent_le hN.le hdisplay)
  have hK2 : N^(ch*aE) ≤ N^display := hnative.trans
    (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hh,hdisplay]))
  exact qualification_display_scalars hH1 hlam hNp htheta0 hres hcost hK2

/-- The qualification display tail precedes all actual clocks,
accuracies, errors and rows, at the fixed native degree. -/
theorem eventually_native_qualification_display_power_budgets
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) (M : ℕ)
    {h thetaFloor analyticPower display : ℝ}
    (hh : 0 < h) (hanalytic0 : 0 ≤ analyticPower)
    (hfloor : 4*h ≤ thetaFloor) (hdisplay : 2*h+analyticPower ≤ display) :
    ∀ᶠ k in atTop, ∀ ch aE theta lam graphError etaFit : ℝ,
      0 < lam → N k^(-thetaFloor) ≤ theta → theta ≤ N k^h →
      graphError ≤ N k^(-2*thetaFloor) → etaFit ≤ N k^(-2*thetaFloor) →
      lam^((M:ℝ)+1/8) ≤ N k^(-2*thetaFloor) → N k^(ch*aE) ≤ N k^analyticPower →
      let qmesh := theta/(8*((M:ℝ)+1))
      let qbound : ℤ := ⌈(3*N k^h+(1+2*N k^h)*N k^(ch*aE))/qmesh⌉+2
      0 < qmesh ∧ 0 ≤ qbound ∧
        3*N k^h+(1+2*N k^h)*N k^(ch*aE) ≤ qmesh*((qbound:ℝ)-1) ∧
        graphError+(1+2*N k^h)*(etaFit+lam^((M:ℝ)+1/8))+((M:ℝ)+1)*qmesh ≤ theta ∧
        Parent.QualificationClock.coefficientCost M*(qmesh*(qbound:ℝ)) ≤ N k^display ∧
        1/N k^display ≤ (lam*N k^(-(ch*aE)))/lam := by
  have hlarge := ((tendsto_rpow_atTop hh).comp hN).eventually
    (eventually_ge_atTop (max 100 (100*Parent.QualificationClock.coefficientCost M)))
  filter_upwards [hN.eventually (eventually_gt_atTop 1),hlarge] with k hk hc
  change max 100 (100*Parent.QualificationClock.coefficientCost M) ≤ N k^h at hc
  intro ch aE theta lam graphError etaFit hlam htheta hthetaH hgraph heta hrem hnative
  exact native_qualification_display_power_budgets M hk hh hanalytic0 hfloor hdisplay
    hlam htheta hthetaH hgraph heta hrem hnative hc

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
