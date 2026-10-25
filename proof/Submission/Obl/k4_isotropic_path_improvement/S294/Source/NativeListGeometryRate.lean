-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeListGeometryRate, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeGeometryProfile
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRecordGeometry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- Every actual list polynomial is covered by the fixed source power. -/
theorem list_geometry_power_le_fixed :
    (3*FixedSourcePowers.coreRadius+65)*FixedSourcePowers.jet+FixedSourcePowers.coreRadius+12 ≤
      FixedSourcePowers.power := by
  have hh := record_geometry_full_power_le
  have heq : 3*FixedSourcePowers.coreRadius+58+7=3*FixedSourcePowers.coreRadius+65 := by omega
  rw [heq] at hh
  omega

/-- The actual census geometry exponent pays every list polynomial,
including the arbitrarily small physical clock factor kappa1. -/
theorem native_list_geometry_rate
    (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    {κ₁ d₁ precision loss gain L delta : ℝ} {Ep : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hbudget : tune.budget κ₁ d₁ Ep precision loss=NativeDesign.budget κ₁ d₁ Ep precision loss)
    (hgain : 0 < gain) (hL : 0 < L) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ tolOf tune κ₁ d₁ Ep precision loss gain) :
    (FixedSourcePowers.power:ℝ)*(3*delta*L) ≤ κ₁*(gain*L)/64 := by
  have hFront := NativeDesign.front_budget_room (Ep:=Ep) hv
  obtain ⟨_hd0,_hd1,hκ,hκ1,_hprecision,hloss,hloss1⟩ := hv
  let B := tune.budget κ₁ d₁ Ep precision loss
  let display := loss*gain*L/((Ep:ℝ)+1)
  have hB : 0 < B := tune.budget_pos _ _ _ _ _
  have hS : 0 < tune.slack := zero_lt_one.trans_le tune.one_le_slack
  have hEp : (1:ℝ) ≤ (Ep:ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) Ep]
  have hdisplay : display ≤ gain*L := by
    dsimp only [display]
    rw [div_le_iff₀ (zero_lt_one.trans_le hEp)]
    have h1 := mul_le_mul_of_nonneg_right hloss1 (mul_nonneg hgain.le hL.le)
    have h2 := mul_le_mul_of_nonneg_left hEp (mul_nonneg hgain.le hL.le)
    nlinarith only [h1,h2]
  have hMass := NativeDesign.massCoeff_le_kappa d₁ (Ep:=Ep) (precision:=precision) hκ hκ1 hloss1
  have hCoef := NativeDesign.coefficient_le_mass_quarter κ₁ d₁ (Ep:=Ep) (precision:=precision) hloss
  rw [←hbudget] at hFront
  have hBκ : B ≤ κ₁/1000000 := by
    dsimp only [B]
    linarith only [hFront,hCoef,hMass,hκ]
  have hAmplitude : B*display ≤ κ₁*(gain*L)/1000000 := by
    calc
      _ ≤ B*(gain*L) := mul_le_mul_of_nonneg_left hdisplay hB.le
      _ ≤ _ := by simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hBκ (mul_nonneg hgain.le hL.le)
  have hTolerance : delta*L*tune.slack ≤ (B*display)/10000 := by
    have hh := mul_le_mul_of_nonneg_right hdelta (by positivity : (0:ℝ) ≤ L*tune.slack)
    have heq : tolOf tune κ₁ d₁ Ep precision loss gain*(L*tune.slack)=B*display/10000 := by
      dsimp only [tolOf,B,display]
      field_simp
    nlinarith only [hh,heq]
  have hPower : (FixedSourcePowers.power:ℝ) ≤ tune.slack := by
    have hh := FixedSourcePowers.slack_pays_power.trans hslack
    have hp : (0:ℝ) ≤ FixedSourcePowers.power := Nat.cast_nonneg _
    linarith only [hh,hp]
  have hCost := mul_le_mul_of_nonneg_left hPower (by positivity : (0:ℝ) ≤ 3*delta*L)
  have hPositive := mul_pos hκ (mul_pos hgain hL)
  nlinarith only [hCost,hTolerance,hAmplitude,hPositive]

/-- The exact polynomial exponent used by `list_powers` fits the
physical list room at the literal census geometry power 3 delta L. -/
theorem native_list_polynomial_rate
    (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    {κ₁ d₁ precision loss gain L delta : ℝ} {Ep : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hbudget : tune.budget κ₁ d₁ Ep precision loss=NativeDesign.budget κ₁ d₁ Ep precision loss)
    (hgain : 0 < gain) (hL : 0 < L) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ tolOf tune κ₁ d₁ Ep precision loss gain) :
    (((3*FixedSourcePowers.coreRadius+65)*FixedSourcePowers.jet+
      FixedSourcePowers.coreRadius+12:ℕ):ℝ)*(3*delta*L) ≤ κ₁*(gain*L)/64 := by
  refine le_trans ?_ (native_list_geometry_rate tune hslack hv hbudget hgain hL hdelta0 hdelta)
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast list_geometry_power_le_fixed
  · positivity

/-- The existing record/source threshold also absorbs the fixed list
constant, so the list lane requires no additional path-dependent tail. -/
theorem native_list_constant_from_source
    {κ₁ d₁ precision loss gainL N : ℝ} {Ep : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hN : 1 ≤ N) (hgainL : 0 < gainL)
    (hlarge : 20000 ≤ N^((NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*gainL)/1000000)) :
    432 ≤ N^(κ₁*gainL/64) := by
  have hκ := hv.2.2.1
  have hm := NativeDesign.massCoeff_le_kappa d₁ (Ep:=Ep) (precision:=precision) hκ hv.2.2.2.1 hv.2.2.2.2.2.2
  have hc := NativeDesign.coefficient_le_mass_quarter κ₁ d₁ (Ep:=Ep) (precision:=precision) hv.2.2.2.2.2.1
  have hcoefficient : NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss ≤ κ₁ := by
    linarith only [hm,hc,hκ]
  have hpower := mul_le_mul_of_nonneg_right hcoefficient hgainL.le
  have hpositive := mul_pos hκ hgainL
  have hexponent : (NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*gainL)/1000000 ≤ κ₁*gainL/64 := by
    nlinarith only [hpower,hpositive]
  exact (by norm_num : (432:ℝ) ≤ 20000).trans
    (hlarge.trans (Real.rpow_le_rpow_of_exponent_le hN hexponent))

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
