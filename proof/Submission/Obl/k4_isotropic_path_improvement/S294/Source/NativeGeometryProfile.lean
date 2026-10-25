-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeGeometryProfile, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeGridProfile
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.RootGeometryPowerBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PencilRadiusScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign

open Parent.Qualification.Jets2
open Parent.Qualification.PhysicalModel

noncomputable section

theorem regularityCoeff_le_mass (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hloss : 0 < loss) :
    regularityCoeff κ₁ d₁ Ep precision loss ≤ massCoeff κ₁ d₁ Ep precision loss/400 := by
  have hm := massCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hL : (1:ℝ) ≤ regularityLength κ₁ d₁ Ep precision loss := by
    exact_mod_cast regularityLength_pos κ₁ d₁ Ep precision loss
  unfold regularityCoeff
  exact div_le_div_of_nonneg_left hm.le (by norm_num) (by nlinarith)

theorem coefficient_le_mass_quarter (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hloss : 0 < loss) :
    coefficientCoeff κ₁ d₁ Ep precision loss ≤ massCoeff κ₁ d₁ Ep precision loss/4 := by
  have hm := massCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hr := regularityCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hh := coefficient_le_regularity κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hh' := regularityCoeff_le_mass κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  linarith

theorem row_coefficient_bounds (κ₁ d₁ : ℝ) {Ep : ℕ} {precision loss : ℝ}
    (hloss : 0 < loss) :
    coefficientCoeff κ₁ d₁ Ep precision loss ≤ regularityCoeff κ₁ d₁ Ep precision loss/1000 ∧
      regularityCoeff κ₁ d₁ Ep precision loss/1000 ≤ massCoeff κ₁ d₁ Ep precision loss/1000 := by
  have hm := massCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hr := regularityCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hh := coefficient_le_regularity κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  have hh' := regularityCoeff_le_mass κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  constructor <;> linarith

/-- The physical error radius is much smaller than the last residual
width, even after the complete geometry polynomial is paid. -/
theorem native_geometry_exponent_room {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss : ℝ}
    (hv : Valid κ₁ d₁ precision loss) :
    massCoeff κ₁ d₁ Ep precision loss+zetaCoeff κ₁ d₁ Ep precision+1 ≤
        (rhoPower κ₁ Ep precision:ℝ)*nativeQualificationDepth d₁ (qualDegree κ₁) ∧
      massCoeff κ₁ d₁ Ep precision loss+rhoCoeff κ₁ d₁ Ep precision+zetaCoeff κ₁ d₁ Ep precision+1 ≤
        graphTargetCoeff κ₁ d₁ Ep precision ∧
      1+rhoCoeff κ₁ d₁ Ep precision+zetaCoeff κ₁ d₁ Ep precision+1 ≤
        graphTargetCoeff κ₁ d₁ Ep precision := by
  have hκ := hv.2.2.1
  have hκ1 := hv.2.2.2.1
  have hprecision := hv.2.2.2.2.1
  have hloss1 := hv.2.2.2.2.2.2
  have hm := massCoeff_le_one κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss1
  have hC : 16 ≤ clockCoeff Ep precision := by
    have hh : (1:ℝ) ≤ ((Ep:ℝ)+1)*precision :=
      one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α:=ℝ) Ep; linarith) hprecision
    unfold clockCoeff
    linarith
  have hC0 : 0 ≤ clockCoeff Ep precision := by linarith
  have hD := one_le_nativeQualificationDepth d₁ (qualDegree κ₁)
  have hD0 : 0 ≤ nativeQualificationDepth d₁ (qualDegree κ₁) := zero_le_one.trans hD
  have hP0 : (0:ℝ) ≤ rhoPower κ₁ Ep precision := Nat.cast_nonneg _
  have hP : 100*clockCoeff Ep precision ≤ (rhoPower κ₁ Ep precision:ℝ) := by
    have hc := Nat.le_ceil (100*clockCoeff Ep precision/κ₁)
    have hh : 100*clockCoeff Ep precision/κ₁ ≤ (rhoPower κ₁ Ep precision:ℝ) := by
      unfold rhoPower
      push_cast
      linarith
    have hh' := (div_le_iff₀ hκ).mp hh
    have hk' := mul_le_mul_of_nonneg_left hκ1 hP0
    nlinarith only [hh',hk']
  have hPD := mul_le_mul_of_nonneg_right hP hD0
  have hCD : 16 ≤ clockCoeff Ep precision*nativeQualificationDepth d₁ (qualDegree κ₁) :=
    hC.trans (le_mul_of_one_le_right hC0 hD)
  have hfirst : massCoeff κ₁ d₁ Ep precision loss+zetaCoeff κ₁ d₁ Ep precision+1 ≤
      (rhoPower κ₁ Ep precision:ℝ)*nativeQualificationDepth d₁ (qualDegree κ₁) := by
    unfold zetaCoeff
    nlinarith only [hPD,hCD,hm]
  have hFloor := floorEndCoeff_pos κ₁ d₁ (Ep:=Ep) hprecision
  have hGraph : floorEndCoeff κ₁ d₁ Ep precision ≤ graphTargetCoeff κ₁ d₁ Ep precision := by
    have hh : 0 ≤ 16*clockCoeff Ep precision/κ₁ := by positivity
    unfold graphTargetCoeff
    linarith
  refine ⟨hfirst,?_,?_⟩
  all_goals unfold floorEndCoeff at hGraph
  all_goals linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

/-- The literal current canonical numerator fits a small native
power at the chosen polynomial coefficient and pure-cell bounds. -/
theorem native_canonical_constant_power {N h e dimension : ℝ}
    (hN : 1 < N) (hlarge : 3000 ≤ N^h) (hdim : dimension ≤ 1) (hhe : 4*h ≤ e) :
    151200*(12*N^h+3)*(N^h)*(3:ℝ)^dimension ≤ N^e := by
  let X := N^h
  have hX : 3000 ≤ X := hlarge
  have hX0 : 0 ≤ X := by linarith
  have h3 : (3:ℝ)^dimension ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 3) hdim
  have hpoly : 151200*(12*X+3)*X*(3:ℝ)^dimension ≤ 6804000*X^2 := by
    calc
      _ ≤ 151200*(15*X)*X*3 := by gcongr; linarith
      _ = _ := by ring
  have hX2 : 6804000 ≤ X^2 := by nlinarith only [hX]
  have hh := mul_le_mul_of_nonneg_right hX2 (sq_nonneg X)
  have hpow : 6804000*X^2 ≤ X^4 := by nlinarith only [hh]
  calc
    _ ≤ X^4 := hpoly.trans hpow
    _ = N^(4*h) := by
      dsimp only [X]
      rw [←Real.rpow_mul_natCast (zero_lt_one.trans hN).le]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN.le hhe

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
