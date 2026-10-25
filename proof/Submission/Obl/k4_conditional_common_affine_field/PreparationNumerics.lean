import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_conditional_common_affine_field

open Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery (eventually_const_mul_rpow_le)

/-- Numerical conditions for `prepare_axes`, with C0=101 and a grid exponent
chosen independently of the loss exponents. -/
structure AxisNumerics (N S A θ h η : ℝ) : Prop where
  N_two : 2 ≤ N
  K_one : 1 ≤ N^η
  H_large : N^η+1 ≤ N^(2*h)
  fine_le_one : N^(-(101*(A+θ))) ≤ 1
  fine_le_grid : N^(-(101*(A+θ))) ≤ N^(-2*(A+θ))
  fine_le_error : N^(-(101*(A+θ))) ≤ N^(-θ)
  fine_le_radius : N^(-(101*(A+θ))) ≤ N^(-h)
  radius_small : 2*N^(-h) ≤ 1
  inverse_H : 1/N^(2*h) ≤ N^(-h)
  grid_le_chart : (N^(2*h)+3)*N^(-2*(A+θ)) ≤ N^(-A)
  fine_le_chart : N^(-(101*(A+θ))) ≤ N^(-A)
  palette_small : (N^η)^2*(2*N^(-h))^S ≤ 1/2

theorem axis_numerics_eventually (S A θ h η : ℝ)
    (hS : 0 < S) (hA : 0 < A) (hθ : 0 < θ) (hh : 0 < h) (hη : 0 < η)
    (hηh : η < h) (hηS : 4*η ≤ h*S) (hhA : 4*h ≤ A+θ) :
    ∀ᶠ N : ℝ in atTop, AxisNumerics N S A θ h η := by
  have hKH := eventually_const_mul_rpow_le 2 (show η < 2*h by linarith)
  have hr := eventually_const_mul_rpow_le 2 (show -h < (0 : ℝ) by linarith)
  have hpal := eventually_const_mul_rpow_le (2*(2 : ℝ)^S)
    (show 2*η-h*S < (0 : ℝ) by linarith)
  have hchart := eventually_const_mul_rpow_le 4
    (show 2*h+(-2*(A+θ)) < -A by linarith)
  filter_upwards [eventually_ge_atTop (2 : ℝ),hKH,hr,hpal,hchart]
    with N hN hKH hr hpal hchart
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hK1 : 1 ≤ N^η := Real.one_le_rpow hN1 hη.le
  have hH1 : 1 ≤ N^(2*h) := Real.one_le_rpow hN1 (by positivity)
  simp only [Real.rpow_zero] at hr hpal
  refine {
    N_two := hN, K_one := hK1
    H_large := ?_
    fine_le_one := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    fine_le_grid := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    fine_le_error := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    fine_le_radius := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    radius_small := hr
    inverse_H := ?_
    grid_le_chart := ?_
    fine_le_chart := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    palette_small := ?_ }
  · linarith
  · rw [one_div,← Real.rpow_neg hNpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  · calc
      _ ≤ (4*N^(2*h))*N^(-2*(A+θ)) := by gcongr; linarith
      _ = 4*N^(2*h+(-2*(A+θ))) := by rw [mul_assoc,← Real.rpow_add hNpos]
      _ ≤ _ := hchart
  · have hid : (N^η)^2*(2*N^(-h))^S = (2 : ℝ)^S*N^(2*η-h*S) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hNpos.le _)]
      rw [← Real.rpow_natCast,← Real.rpow_mul hNpos.le,← Real.rpow_mul hNpos.le]
      rw [mul_left_comm,← Real.rpow_add hNpos]
      congr 1
      ring
    rw [hid]
    nlinarith only [hpal]

/-- Arbitrarily many fixed loss powers fit below both the output loss and the
original fixed fine-state horizon. The input exponent is selected last. -/
theorem exists_small_preparation_exponents (S A θ ε M : ℝ)
    (hS : 0 < S) (hA : 0 < A) (hθ : 0 < θ) (hε : 0 < ε) (hM : 0 ≤ M) :
    ∃ h η : ℝ, 0 < h ∧ 0 < η ∧ η ≤ ε ∧ η < h ∧
      4*η ≤ h*S ∧ 4*h ≤ A+θ ∧ M*h < ε ∧ M*h < A+θ ∧ M*h < S*(A+θ) := by
  let B := 10*(M+1)
  have hB : 0 < B := by dsimp [B]; positivity
  let h := min (ε/B) (min ((A+θ)/B) (S*(A+θ)/B))
  have hh : 0 < h := by dsimp [h]; positivity
  have hhε : B*h ≤ ε := by
    have hx : h ≤ ε/B := min_le_left _ _
    have hx' := (le_div_iff₀ hB).mp hx
    nlinarith
  have hhA : B*h ≤ A+θ := by
    have hx : h ≤ (A+θ)/B := (min_le_right _ _).trans (min_le_left _ _)
    have hx' := (le_div_iff₀ hB).mp hx
    nlinarith
  have hhS : B*h ≤ S*(A+θ) := by
    have hx : h ≤ S*(A+θ)/B := (min_le_right _ _).trans (min_le_right _ _)
    have hx' := (le_div_iff₀ hB).mp hx
    nlinarith
  have hMh : M*h < B*h := by
    dsimp [B]
    nlinarith [mul_nonneg hM hh.le]
  have h4h : 4*h ≤ B*h := by
    dsimp [B]
    nlinarith [mul_nonneg hM hh.le]
  let η := min ε (min (h/10) (h*S/10))/2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η ≤ ε := by
    have h := min_le_left ε (min (h/10) (h*S/10))
    dsimp [η]
    linarith
  have hηh : η ≤ h/20 := by
    have hx := (min_le_right ε (min (h/10) (h*S/10))).trans (min_le_left _ _)
    dsimp [η]
    linarith
  have hηS : η ≤ h*S/20 := by
    have hx := (min_le_right ε (min (h/10) (h*S/10))).trans (min_le_right _ _)
    dsimp [η]
    linarith
  refine ⟨h,η,hh,hη,hηε,by linarith,?_,h4h.trans hhA,
    hMh.trans_le hhε,hMh.trans_le hhA,hMh.trans_le hhS⟩
  nlinarith [mul_pos hh hS]

/-- One fixed power budget simultaneously controls coefficients, fitting loss,
and the requested original mass floor. -/
theorem loss_budget_eventually (C h ε : ℝ) (P : ℕ)
    (hC : 0 < C) (hgap : 2*h*(P : ℝ) < ε) :
    ∀ᶠ N : ℝ in atTop, C*(N^(2*h))^P ≤ N^ε ∧
      N^(-ε) ≤ 1/(C*(N^(2*h))^P) := by
  have hpow := eventually_const_mul_rpow_le C hgap
  filter_upwards [eventually_ge_atTop (2 : ℝ),hpow] with N hN hpow
  have hNpos : 0 < N := by linarith
  have hident : (N^(2*h))^P = N^(2*h*(P : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hNpos.le]
  have hbound : C*(N^(2*h))^P ≤ N^ε := by simpa only [hident] using hpow
  refine ⟨hbound,?_⟩
  rw [Real.rpow_neg hNpos.le,← one_div]
  exact one_div_le_one_div_of_le (by positivity) hbound

/-- The product grid is fine enough for every fixed loss power once its exponent
has been chosen below the original geometric rates. -/
theorem mesh_budget_eventually (C A θ h : ℝ) (P : ℕ)
    (hgap : 2*h*(P : ℝ)-2*(A+θ) < -θ) :
    ∀ᶠ N : ℝ in atTop, C*(N^(2*h))^P*N^(-2*(A+θ)) ≤ N^(-θ) := by
  have hpow := eventually_const_mul_rpow_le C hgap
  filter_upwards [eventually_ge_atTop (2 : ℝ),hpow] with N hN hpow
  have hNpos : 0 < N := by linarith
  have hident : (N^(2*h))^P = N^(2*h*(P : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hNpos.le]
  rw [hident,mul_assoc,← Real.rpow_add hNpos]
  simpa only [sub_eq_add_neg,neg_mul] using hpow

end Submission.Obl.k4_conditional_common_affine_field
