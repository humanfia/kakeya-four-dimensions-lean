import Submission.Obl.k4_conditional_common_affine_field.PreparationNumerics
import Submission.Obl.k4_conditional_common_affine_field.ReturnEstimates

namespace Submission.Obl.k4_conditional_common_affine_field

open Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery (eventually_const_mul_rpow_le)

noncomputable def avoidExponent (S h : ℝ) (P : ℕ) : ℝ := 20*h*((P : ℝ)+10)/S

structure ReturnNumerics (N S A θ h η ε : ℝ) (P : ℕ) : Prop extends AxisNumerics N S A θ h η where
  budget_large : 1000 ≤ N^(20*h)
  axes_to_budget : 2*N^(2*h) ≤ N^(20*h)
  menus_to_budget : 25*N^η ≤ N^(20*h)
  mass_to_budget : 2*(N^η)^3 ≤ N^(20*h)
  cap_to_budget : (12*(N^(2*h))^2+11)^2*N^η ≤ N^(20*h)
  grid_small : N^(-2*(A+θ)) ≤ ((N^(20*h))^P)⁻¹
  grid_le_error : N^(-2*(A+θ)) ≤ N^(-θ)
  fine_le_avoid : N^(-(101*(A+θ))) ≤ N^(-avoidExponent S h P)
  avoid_small : 4*N^(-avoidExponent S h P) ≤ 1
  pencil_small : 4*((N^η)^3*(4*N^(-avoidExponent S h P))^S) ≤ ((N^(20*h))^P)⁻¹
  final_loss : (N^(20*h))^(returnDegree P)/(N^(-avoidExponent S h P))^2 ≤ N^ε
  final_coefficient : (N^(20*h))^(returnDegree P) ≤ N^ε
  final_mass : N^(-ε) ≤ ((N^(20*h))^P)⁻¹

set_option maxHeartbeats 800000 in
theorem return_numerics_eventually (S A θ h η ε : ℝ) (P : ℕ)
    (hS : 0 < S) (hA : 0 < A) (hθ : 0 < θ) (hh : 0 < h) (hη : 0 < η)
    (hηh : η < h) (hηS : 4*η ≤ h*S) (hhA : 4*h ≤ A+θ)
    (haA : avoidExponent S h P < A+θ)
    (hgrid : 20*h*(P : ℝ) < 2*(A+θ))
    (hfinal : 20*h*(returnDegree P : ℝ)+2*avoidExponent S h P < ε) :
    ∀ᶠ N : ℝ in atTop, ReturnNumerics N S A θ h η ε P := by
  let a := avoidExponent S h P
  have ha : 0 < a := by dsimp [a,avoidExponent]; positivity
  have haS : a*S=20*h*((P : ℝ)+10) := by dsimp [a,avoidExponent]; field_simp
  have hinit := axis_numerics_eventually S A θ h η hS hA hθ hh hη hηh hηS hhA
  have hlarge := eventually_const_mul_rpow_le 1000 (show (0 : ℝ) < 20*h by positivity)
  have haxes := eventually_const_mul_rpow_le 2 (show 2*h < 20*h by linarith)
  have hmenus := eventually_const_mul_rpow_le 25 (show η < 20*h by linarith)
  have hmass := eventually_const_mul_rpow_le 2 (show 3*η < 20*h by linarith)
  have hcap := eventually_const_mul_rpow_le 529 (show 8*h+η < 20*h by linarith)
  have havoid := eventually_const_mul_rpow_le 4 (show -a < (0 : ℝ) by linarith)
  have hpencil := eventually_const_mul_rpow_le (4*(4 : ℝ)^S)
    (show 3*η-a*S < -(20*h*(P : ℝ)) by rw [haS]; nlinarith)
  filter_upwards [hinit,hlarge,haxes,hmenus,hmass,hcap,havoid,hpencil]
    with N hinit hlarge haxes hmenus hmass hcap havoid hpencil
  have hNpos : 0 < N := by linarith [hinit.N_two]
  have hN1 : 1 ≤ N := by linarith [hinit.N_two]
  have hH1 : 1 ≤ N^(2*h) := Real.one_le_rpow hN1 (by positivity)
  have hK0 : 0 ≤ N^η := Real.rpow_nonneg hNpos.le _
  have hH0 : 0 ≤ N^(2*h) := Real.rpow_nonneg hNpos.le _
  have hpowers (q : ℝ) (n : ℕ) : (N^q)^n=N^(q*(n : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hNpos.le]
  have hInv : ((N^(20*h))^P)⁻¹=N^(-(20*h*(P : ℝ))) := by
    rw [hpowers]
    exact (Real.rpow_neg hNpos.le _).symm
  simp only [Real.rpow_zero, mul_one] at hlarge havoid
  refine {
    toAxisNumerics := hinit
    budget_large := hlarge, axes_to_budget := haxes, menus_to_budget := hmenus
    mass_to_budget := ?_, cap_to_budget := ?_, grid_small := ?_
    grid_le_error := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    fine_le_avoid := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    avoid_small := havoid
    pencil_small := ?_, final_loss := ?_, final_coefficient := ?_, final_mass := ?_ }
  · rw [hpowers]
    convert hmass using 1
    congr 2
    ring
  · have hHsq : 1 ≤ (N^(2*h))^2 := one_le_pow₀ hH1
    have hscale : 12*(N^(2*h))^2+11 ≤ 23*(N^(2*h))^2 := by linarith
    have hsquared := pow_le_pow_left₀ (by positivity : 0 ≤ 12*(N^(2*h))^2+11) hscale 2
    calc
      _ ≤ (23*(N^(2*h))^2)^2*N^η := mul_le_mul_of_nonneg_right hsquared hK0
      _ = 529*(N^(2*h))^4*N^η := by ring
      _ = 529*N^(8*h+η) := by rw [hpowers,mul_assoc,← Real.rpow_add hNpos]; congr 1; ring
      _ ≤ _ := hcap
  · rw [hInv]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  · have hid : 4*((N^η)^3*(4*N^(-a))^S)=(4*(4 : ℝ)^S)*N^(3*η-a*S) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg hNpos.le _)]
      rw [hpowers,← Real.rpow_mul hNpos.le]
      calc
        _ = (4*(4 : ℝ)^S)*(N^(η*3)*N^(-a*S)) := by ring
        _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring
    rw [hid,hInv]
    exact hpencil
  · have hid : (N^(20*h))^(returnDegree P)/(N^(-a))^2 =
        N^(20*h*(returnDegree P : ℝ)+2*a) := by
      rw [hpowers,hpowers,← Real.rpow_sub hNpos]
      congr 1
      ring
    rw [hid]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hfinal.le
  · rw [hpowers]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  · rw [hInv]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hdeg : (P : ℝ) ≤ (returnDegree P : ℝ) := by exact_mod_cast (by dsimp [returnDegree]; omega : P ≤ returnDegree P)
    nlinarith [mul_le_mul_of_nonneg_left hdeg (show 0 ≤ 20*h by positivity)]

theorem exists_return_parameters (S A θ ε : ℝ) (P : ℕ)
    (hS : 0 < S) (hA : 0 < A) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ h η : ℝ, 0 < h ∧ 0 < η ∧ η ≤ ε ∧
      ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ReturnNumerics N S A θ h η ε P := by
  let M := 20*(returnDegree P : ℝ)+40*((P : ℝ)+10)/S+20*((P : ℝ)+10)+100
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨h,η,hh,hη,hηε,hηh,hηS,hhA,hMε,hMA,hMS⟩ :=
    exists_small_preparation_exponents S A θ ε M hS hA hθ hε hM
  have hMpart : 20*((P : ℝ)+10) ≤ M := by
    have h1 : 0 ≤ 20*(returnDegree P : ℝ) := by positivity
    have h2 : 0 ≤ 40*((P : ℝ)+10)/S := by positivity
    dsimp [M]
    linarith
  have haA : avoidExponent S h P < A+θ := by
    apply (div_lt_iff₀ hS).mpr
    exact (by nlinarith [mul_le_mul_of_nonneg_right hMpart hh.le] :
      20*h*((P : ℝ)+10) < (A+θ)*S)
  have hgrid : 20*h*(P : ℝ) < 2*(A+θ) := by
    have hnat : 0 ≤ (P : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hMpart hh.le]
  have hfinal : 20*h*(returnDegree P : ℝ)+2*avoidExponent S h P < ε := by
    have hid : M*h = (20*h*(returnDegree P : ℝ)+2*avoidExponent S h P)+
        (20*((P : ℝ)+10)+100)*h := by dsimp [M,avoidExponent]; ring
    rw [hid] at hMε
    nlinarith [mul_pos (show 0 < 20*((P : ℝ)+10)+100 by positivity) hh]
  have hevent := return_numerics_eventually S A θ h η ε P
    hS hA hθ hh hη hηh hηS hhA haA hgrid hfinal
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨h,η,hh,hη,hηε,max 2 N₀,le_max_left _ _,?_⟩
  intro N hN
  exact hN₀ N ((le_max_right _ _).trans hN)

end Submission.Obl.k4_conditional_common_affine_field
