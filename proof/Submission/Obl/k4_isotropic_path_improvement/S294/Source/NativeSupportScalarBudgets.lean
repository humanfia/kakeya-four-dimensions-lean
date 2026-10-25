-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeSupportScalarBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.WorldScalarSupportPreparation

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.Qualification.PhysicalModel
open Filter

noncomputable section

private theorem natural_power_of_rpow {N a : ℝ} (hN : 0 < N) (n : ℕ) :
    (N^a)^n=N^(a*(n:ℝ)) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]

/-- The literal original support filling inequality is paid by the
proposed Hprior, Kfill and support-radius powers. -/
theorem native_fill_power_budget {N e Cmk radius : ℝ}
    (hN : 1 ≤ N) (he : 0 < e) (hlarge : (10:ℝ)^100 ≤ N^e)
    (hCmk : 0 ≤ Cmk) (hCmkN : Cmk ≤ N^(e/1000))
    (hradius : N^(-(e/1000)) ≤ radius) :
    (8*Cmk*7^3)^2*(3*N^(4*e))^3 ≤
      ((radius/2)^3/2*(1-(1/2:ℝ))^3)*N^(16*e) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hradius0 : 0 < radius := (Real.rpow_pos_of_pos hNp _).trans_le hradius
  have hconstant : (128*((8*7^3)^2*27):ℝ) ≤ N^e := by norm_num at hlarge ⊢; linarith only [hlarge]
  have hleft : (8*Cmk*7^3)^2*(3*N^(4*e))^3 ≤
      (((8*7^3)^2*27):ℝ)*N^(2*(e/1000)+12*e) := by
    calc
      _ ≤ (8*N^(e/1000)*7^3)^2*(3*N^(4*e))^3 := by gcongr
      _ = (((8*7^3)^2*27):ℝ)*((N^(e/1000))^2*(N^(4*e))^3) := by ring
      _ = _ := by
        rw [natural_power_of_rpow hNp 2,natural_power_of_rpow hNp 3,←Real.rpow_add hNp]
        congr 2
        norm_num
        ring
  have hright : N^(16*e-3*(e/1000))/128 ≤
      ((radius/2)^3/2*(1-(1/2:ℝ))^3)*N^(16*e) := by
    calc
      _ = ((N^(-(e/1000)))^3)*N^(16*e)/128 := by
        rw [natural_power_of_rpow hNp 3,←Real.rpow_add hNp]
        congr 2
        norm_num
        ring
      _ ≤ radius^3*N^(16*e)/128 := by gcongr
      _ = _ := by ring
  apply le_trans _ hright
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 128)]
  calc
    _ ≤ ((((8*7^3)^2*27):ℝ)*N^(2*(e/1000)+12*e))*128 :=
      mul_le_mul_of_nonneg_right hleft (by norm_num)
    _ = (128*((8*7^3)^2*27):ℝ)*N^(2*(e/1000)+12*e) := by ring
    _ ≤ N^e*N^(2*(e/1000)+12*e) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hNp.le _)
    _ = N^(e+2*(e/1000)+12*e) := by rw [←Real.rpow_add hNp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [he])

/-- The actual world scalar support constant has a uniform small
power at the literal rate and filling choices. -/
theorem native_world_support_power_budget {N e h B : ℝ}
    (hN : 1 ≤ N) (he : 0 < e) (hlarge : (10:ℝ)^100 ≤ N^e)
    (hsmall : h ≤ e/1000000) (hB : 1 ≤ B) (hBN : B ≤ N^(e/1000)) :
    worldScalarSupportConstant B (N^h) (N^(-4*e)) (N^(16*e)) 2 ≤ N^(24*e) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hB2 : 1 ≤ B^2 := one_le_pow₀ hB
  have hBsquare : B ≤ B^2 := by nlinarith only [mul_le_mul_of_nonneg_left hB hB0]
  have houter : 2*(4*B^2+3*B)+2 ≤ 16*B^2 := by linarith only [hBsquare,hB2]
  have hinner : 8+6*B ≤ 14*B := by linarith only [hB]
  have hconstant : ((16:ℝ)*27^4*(67584000*8*14)*2) ≤ N^e := by
    norm_num at hlarge ⊢
    linarith only [hlarge]
  have hB4 : B^4 ≤ N^(4*(e/1000)) := by
    calc
      _ ≤ (N^(e/1000))^4 := pow_le_pow_left₀ hB0 hBN 4
      _ = _ := by rw [natural_power_of_rpow hNp 4]; congr 1; norm_num; ring
  have hmonomial : worldScalarSupportConstant B (N^h) (N^(-4*e)) (N^(16*e)) 2 ≤
      ((16:ℝ)*27^4*(67584000*8*14)*2)*N^(20*e+4*(e/1000)+h) := by
    unfold worldScalarSupportConstant
    calc
      _ ≤ (16*B^2)*((27:ℝ)^4*(67584000*B*(8*N^h/N^(-4*e))*N^(16*e)*(14*B))*2) := by gcongr
      _ = ((16:ℝ)*27^4*(67584000*8*14)*2)*
          (((B^4*N^(4*e))*N^(16*e))*N^h) := by
        rw [show -4*e=-(4*e) by ring,Real.rpow_neg hNp.le,div_inv_eq_mul]
        ring
      _ ≤ ((16:ℝ)*27^4*(67584000*8*14)*2)*
          (((N^(4*(e/1000))*N^(4*e))*N^(16*e))*N^h) := by gcongr
      _ = _ := by
        rw [←Real.rpow_add hNp,←Real.rpow_add hNp,←Real.rpow_add hNp]
        congr 2
        ring
  calc
    _ ≤ ((16:ℝ)*27^4*(67584000*8*14)*2)*N^(20*e+4*(e/1000)+h) := hmonomial
    _ ≤ N^e*N^(20*e+4*(e/1000)+h) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hNp.le _)
    _ = N^(e+(20*e+4*(e/1000)+h)) := (Real.rpow_add hNp _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [he,hsmall])

/-- The exact native cap and residual-smallness conditions follow
from the displayed original powers, uniformly above nativeMin. -/
theorem native_cap_residual_power_budgets {N e ar nativeMin native : ℝ}
    (hN : 1 ≤ N) (he : 0 < e) (hlarge : (10:ℝ)^100 ≤ N^e)
    (hnative : 100*e ≤ nativeMin) (har : 8*ar ≤ nativeMin) (hmin : nativeMin ≤ native) :
    8*(N^(8*e))^2 ≤ N^native ∧ 2*(N^ar+5*(N^(2*e))^2) ≤ N^native := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have h8 : (8:ℝ) ≤ N^e := by norm_num at hlarge ⊢; linarith only [hlarge]
  have h12 : (12:ℝ) ≤ N^e := by norm_num at hlarge ⊢; linarith only [hlarge]
  have hp8 : (N^(8*e))^2=N^(16*e) := by
    rw [natural_power_of_rpow hNp 2]; congr 1; norm_num; ring
  have hp2 : (N^(2*e))^2=N^(4*e) := by
    rw [natural_power_of_rpow hNp 2]; congr 1; norm_num; ring
  constructor
  · rw [hp8]
    calc
      _ ≤ N^e*N^(16*e) := mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg hNp.le _)
      _ = N^(17*e) := by rw [←Real.rpow_add hNp]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hnative,hmin,he])
  · rw [hp2]
    have hA : N^ar ≤ N^(max ar (4*e)) := Real.rpow_le_rpow_of_exponent_le hN (le_max_left _ _)
    have hR : N^(4*e) ≤ N^(max ar (4*e)) := Real.rpow_le_rpow_of_exponent_le hN (le_max_right _ _)
    calc
      _ ≤ 12*N^(max ar (4*e)) := by linarith only [hA,hR]
      _ ≤ N^e*N^(max ar (4*e)) := mul_le_mul_of_nonneg_right h12 (Real.rpow_nonneg hNp.le _)
      _ = N^(e+max ar (4*e)) := (Real.rpow_add hNp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by
        have hh : max ar (4*e) ≤ native-e := max_le
          (by linarith only [har,hnative,hmin,he]) (by linarith only [hnative,hmin,he])
        linarith only [hh])

/-- A common tail supplies the original fill, support, cap and
residual-smallness budgets, uniformly in the later native clock
exponent and every actual support radius and row bound. -/
theorem eventually_native_support_scalar_budgets
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {e h ar nativeMin : ℝ} (he : 0 < e) (hsmall : h ≤ e/1000000)
    (hnative : 100*e ≤ nativeMin) (har : 8*ar ≤ nativeMin) :
    ∀ᶠ k in atTop, ∀ native B Cmk radius : ℝ,
      nativeMin ≤ native → 1 ≤ B → B ≤ N k^(e/1000) →
      0 ≤ Cmk → Cmk ≤ N k^(e/1000) → N k^(-(e/1000)) ≤ radius →
      (8*Cmk*7^3)^2*(3*N k^(4*e))^3 ≤
        ((radius/2)^3/2*(1-(1/2:ℝ))^3)*N k^(16*e) ∧
      worldScalarSupportConstant B (N k^h) (N k^(-4*e)) (N k^(16*e)) 2 ≤ N k^native ∧
      8*(N k^(8*e))^2 ≤ N k^native ∧
      2*(N k^ar+5*(N k^(2*e))^2) ≤ N k^native := by
  have hlarge := ((tendsto_rpow_atTop he).comp hN).eventually
    (eventually_ge_atTop ((10:ℝ)^100))
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  change (10:ℝ)^100 ≤ N k^e at hc
  intro native B Cmk radius hmin hB hBN hCmk hCmkN hradius
  have hfill := native_fill_power_budget hk he hc hCmk hCmkN hradius
  have hss := native_world_support_power_budget hk he hc hsmall hB hBN
  have hssNative : worldScalarSupportConstant B (N k^h) (N k^(-4*e)) (N k^(16*e)) 2 ≤ N k^native :=
    hss.trans (Real.rpow_le_rpow_of_exponent_le hk (by linarith only [hnative,hmin,he]))
  obtain ⟨hcap,hres⟩ := native_cap_residual_power_budgets hk he hc hnative har hmin
  exact ⟨hfill,hssNative,hcap,hres⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
