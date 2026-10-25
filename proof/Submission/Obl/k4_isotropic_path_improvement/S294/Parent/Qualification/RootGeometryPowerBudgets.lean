-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.RootGeometryPowerBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.RootGeometryBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

/-- The concrete regularity Lipschitz constant and the complete
geometry polynomial fit one small original power. -/
theorem root_geometry_constant_power {N e H B : ℝ} (hN : 1 < N)
    (hlarge : 100 ≤ N^(e/4)) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hHbound : H ≤ N^(e/4)) (hBbound : B ≤ N^(e/4)) :
    let Lp := 6*(N^(e/4)+3*B)
    0 ≤ Lp ∧ Lp ≤ N^(e/2) ∧ rootGeometryConstant H B Lp ≤ N^e ∧
      3*((3*H+1)*Lp) ≤ N^(2*e) := by
  intro Lp
  let X := N^(e/4)
  have hX : 100 ≤ X := hlarge
  have hX0 : 0 ≤ X := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hLp0 : 0 ≤ Lp := by dsimp only [Lp]; positivity
  have hLp : Lp ≤ 24*X := by dsimp only [Lp,X]; nlinarith only [hBbound]
  have hconst : rootGeometryConstant H B Lp ≤ rootGeometryConstant X X (24*X) := by
    unfold rootGeometryConstant
    gcongr
  have hpoly : rootGeometryConstant X X (24*X) ≤ 10000*X^2 := by
    unfold rootGeometryConstant
    nlinarith only [hX]
  have hXsq : 10000 ≤ X^2 := by nlinarith only [hX]
  have hpoly2 : 10000*X^2 ≤ X^4 := by
    have hh := mul_le_mul_of_nonneg_right hXsq (sq_nonneg X)
    nlinarith only [hh]
  have hX2 : X^2=N^(e/2) := by
    dsimp only [X]
    rw [←Real.rpow_mul_natCast (zero_lt_one.trans hN).le]
    congr 1
    ring
  have hX4 : X^4=N^e := by
    dsimp only [X]
    rw [←Real.rpow_mul_natCast (zero_lt_one.trans hN).le]
    congr 1
    ring
  have hgeometry : rootGeometryConstant H B Lp ≤ N^e := by
    rw [←hX4]
    exact hconst.trans (hpoly.trans hpoly2)
  have he : 0 ≤ e := by
    by_contra hh
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith : e/4 ≤ 0)
    linarith
  have hrow : 3*((3*H+1)*Lp) ≤ rootGeometryConstant H B Lp := by
    unfold rootGeometryConstant
    nlinarith only [hH,hB,hLp0,mul_nonneg hH0 hLp0]
  refine ⟨hLp0,?_,hgeometry,hrow.trans (hgeometry.trans ?_)⟩
  · rw [←hX2]
    nlinarith only [hLp,hX]
  · exact Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)

/-- Polynomial scalar floors imply the three original geometric
smallness comparisons, uniformly over all grid and clock choices. -/
theorem root_geometry_small_of_power_bounds {N C e target r l upper margin rho last b error : ℝ}
    (hN : 1 < N) (hC : C ≤ N^e) (hrho : 0 ≤ rho) (hlast : 0 ≤ last) (hb : 0 ≤ b)
    (hrhoLo : N^(-r) ≤ rho) (hrhoHi : rho ≤ N^(-upper))
    (hlastLo : N^(-l) ≤ last) (hbHi : b ≤ N^(-target)) (heHi : error ≤ N^(-target))
    (hrhoRoom : e+l ≤ upper) (hbRoom : e+r+l ≤ target)
    (heRoom : margin+r+l ≤ target) (hlarge : 16 ≤ N^margin) :
    C*rho ≤ last ∧ C*b ≤ rho*last ∧ 16*error ≤ rho*last := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hproduct : N^(-(r+l)) ≤ rho*last := by
    calc
      _=N^(-r)*N^(-l) := by rw [←Real.rpow_add hNp] <;> congr 1 <;> ring
      _ ≤ _ := mul_le_mul hrhoLo hlastLo (by positivity) hrho
  refine ⟨?_,?_,?_⟩
  · calc
      C*rho ≤ N^e*N^(-upper) := mul_le_mul hC hrhoHi hrho (by positivity)
      _=N^(e-upper) := by rw [←Real.rpow_add hNp] <;> congr 1 <;> ring
      _ ≤ N^(-l) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
      _ ≤ last := hlastLo
  · calc
      C*b ≤ N^e*N^(-target) := mul_le_mul hC hbHi hb (by positivity)
      _=N^(e-target) := by rw [←Real.rpow_add hNp] <;> congr 1 <;> ring
      _ ≤ N^(-(r+l)) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
      _ ≤ rho*last := hproduct
  · calc
      16*error ≤ 16*N^(-target) := mul_le_mul_of_nonneg_left heHi (by norm_num)
      _ ≤ N^margin*N^(-target) := mul_le_mul_of_nonneg_right hlarge (by positivity)
      _=N^(margin-target) := by rw [←Real.rpow_add hNp] <;> congr 1 <;> ring
      _ ≤ N^(-(r+l)) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
      _ ≤ rho*last := hproduct

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
