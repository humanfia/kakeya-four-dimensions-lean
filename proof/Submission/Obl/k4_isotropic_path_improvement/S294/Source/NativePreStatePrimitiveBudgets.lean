-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativePreStatePrimitiveBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalPreStateScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.Qualification Filter

noncomputable section

private theorem primitive_caps_base {X d : ℝ}
    (hX : (10:ℝ)^100 ≤ X) (hd : d ≤ 1) :
    2*X ≤ X^2 ∧ Jets2.originalParameterCapConstant X (4200*(12*X+3)*X) d ≤ X^8 ∧
      4*(4*X+6)^3*(((12*X+2)*X)*X^100) ≤ X^106 := by
  have hX1 : 1 ≤ X := by linarith only [hX]
  have hX0 : 0 ≤ X := zero_le_one.trans hX1
  have h15 : 12*X+3 ≤ 15*X := by linarith only [hX1]
  have h4 : 2+2*X ≤ 4*X := by linarith only [hX1]
  have h12 : (6+6*X)^d ≤ 12*X := by
    calc
      _ ≤ (6+6*X)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hX1]) hd
      _ ≤ _ := by rw [Real.rpow_one]; linarith only [hX1]
  have h2 : X+1 ≤ 2*X := by linarith only [hX1]
  have hConst1 : (96768000:ℝ) ≤ X := by norm_num at hX ⊢; linarith only [hX]
  have hConst2 : (56000:ℝ) ≤ X := by norm_num at hX ⊢; linarith only [hX]
  refine ⟨?_,?_,?_⟩
  · have hh : (2:ℝ) ≤ X := by linarith only [hX]
    nlinarith only [mul_le_mul_of_nonneg_right hh hX0]
  · unfold Jets2.originalParameterCapConstant
    calc
      _ ≤ 2*(2*(4200*(15*X)*X)*X*(4*X)^2*(12*X))*(2*X) := by gcongr
      _ = 96768000*X^7 := by ring
      _ ≤ X*X^7 := mul_le_mul_of_nonneg_right hConst1 (by positivity)
      _ = _ := by ring
  · have h10 : 4*X+6 ≤ 10*X := by linarith only [hX1]
    have h14 : 12*X+2 ≤ 14*X := by linarith only [hX1]
    calc
      _ ≤ 4*(10*X)^3*(((14*X)*X)*X^100) := by gcongr
      _ = 56000*X^105 := by ring
      _ ≤ X*X^105 := mul_le_mul_of_nonneg_right hConst2 (by positivity)
      _ = _ := by ring

private theorem derivative_poly_base {X d : ℝ}
    (hX : (10:ℝ)^100 ≤ X) (hd : d ≤ 1) :
    let H := ⌈X⌉₊
    (2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
      (151200*(12*(H:ℝ)+3)*X*(3:ℝ)^d)*
        (2*(⌈2*(H:ℝ)+5⌉:ℝ)+1) ≤ X^15 := by
  let H := ⌈X⌉₊
  have hX1 : 1 ≤ X := by linarith only [hX]
  have hX0 : 0 ≤ X := zero_le_one.trans hX1
  have hceil := (Nat.ceil_lt_add_one hX0).le
  have hH : (H:ℝ) ≤ 2*X := by dsimp only [H]; linarith only [hceil,hX1]
  have h7 : 2*(H:ℝ)+3 ≤ 7*X := by linarith only [hH,hX1]
  have h24 : 6*(H:ℝ)+12 ≤ 24*X := by linarith only [hH,hX1]
  have h27 : 12*(H:ℝ)+3 ≤ 27*X := by linarith only [hH,hX1]
  have h3 : (3:ℝ)^d ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hd
  have hInt := (Int.ceil_lt_add_one (2*(H:ℝ)+5)).le
  have h21 : 2*(⌈2*(H:ℝ)+5⌉:ℝ)+1 ≤ 21*X := by linarith only [hInt,hH,hX1]
  have hConst : ((7:ℝ)^7*24^4*(151200*27*3)*21) ≤ X := by
    norm_num at hX ⊢
    linarith only [hX]
  change (2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
    (151200*(12*(H:ℝ)+3)*X*(3:ℝ)^d)*(2*(⌈2*(H:ℝ)+5⌉:ℝ)+1) ≤ X^15
  calc
    _ ≤ (7*X)^7*(24*X)^4*(151200*(27*X)*X*3)*(21*X) := by gcongr
    _ = ((7:ℝ)^7*24^4*(151200*27*3)*21)*X^14 := by ring
    _ ≤ X*X^14 := mul_le_mul_of_nonneg_right hConst (by positivity)
    _ = _ := by ring

/-- All three literal original coefficient-floor budgets follow
from the design's power reserve, including the exact cap constant. -/
theorem native_prestate_floor_budgets
    {N h b eta width d : ℝ} (hN : 1 ≤ N) (hh : 0 < h)
    (hlarge : (10:ℝ)^100 ≤ N^h) (heta : 0 < eta) (hwidth : 0 < width)
    (hwidthN : width ≤ N^(-b)) (hd : d ≤ 1) (hreserve : 200*h ≤ b*eta) :
    2*N^h ≤ width^(-eta) ∧
      Jets2.originalParameterCapConstant (N^h) (4200*(12*N^h+3)*N^h) d ≤ width^(-eta) ∧
      4*(4*N^h+6)^3*(((12*N^h+2)*N^h)*N^(100*h)) ≤ width^(-eta) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hp (n : ℕ) : (N^h)^n=N^((n:ℝ)*h) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]; congr 1; ring
  obtain ⟨h2,h8,h106⟩ := primitive_caps_base hlarge hd
  have htarget : N^(200*h) ≤ width^(-eta) := by
    calc
      _ ≤ N^(b*eta) := Real.rpow_le_rpow_of_exponent_le hN hreserve
      _ = (N^(-b))^(-eta) := by
        rw [←Real.rpow_mul hNp.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hwidth hwidthN (neg_nonpos.mpr heta.le)
  have h2p : (N^h)^2 ≤ N^(200*h) := by
    rw [hp]
    apply Real.rpow_le_rpow_of_exponent_le hN
    norm_num
    linarith only [hh]
  have h8p : (N^h)^8 ≤ N^(200*h) := by
    rw [hp]
    apply Real.rpow_le_rpow_of_exponent_le hN
    norm_num
    linarith only [hh]
  have h106p : (N^h)^106 ≤ N^(200*h) := by
    rw [hp]
    apply Real.rpow_le_rpow_of_exponent_le hN
    norm_num
    linarith only [hh]
  refine ⟨h2.trans (h2p.trans htarget),h8.trans (h8p.trans htarget),?_⟩
  have hp100 : (N^h)^100=N^(100*h) := by simpa only [Nat.cast_ofNat] using hp 100
  rw [hp100] at h106
  exact h106.trans (h106p.trans htarget)

/-- The actual derivative-table list budget, including the coarse
fallback and both ceilings, follows from fixed linear exponent room. -/
theorem native_prestate_derivative_list_bound
    {N h b E epsilon widthStart widthReg cut u d : ℝ}
    (hN : 1 ≤ N) (hh : 0 < h) (hb : 0 ≤ b)
    (hlarge : (10:ℝ)^100 ≤ N^h) (hepsilon : 0 ≤ epsilon)
    (hwidthStart : N^(-b)/2 ≤ widthStart) (hwidthReg : N^(-E) ≤ widthReg)
    (hcut : N^(-h) ≤ cut) (hd : d ≤ 1)
    (hcoarseBudget : 2*h+b ≤ u) (hfineBudget : 16*h+E*epsilon ≤ u) :
    let H := ⌈N^h⌉₊
    max (6*(H:ℝ)/widthStart+2)
      ((2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
        ((151200*(12*(H:ℝ)+3)*N^h*(3:ℝ)^d)*widthReg^(-epsilon)/cut)*
          (2*(⌈2*(H:ℝ)+5⌉:ℝ)+1)) ≤ N^u := by
  let H := ⌈N^h⌉₊
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hX1 : 1 ≤ N^h := Real.one_le_rpow hN hh.le
  have hX0 : 0 ≤ N^h := (Real.rpow_pos_of_pos hNp _).le
  have hb1 : 1 ≤ N^b := Real.one_le_rpow hN hb
  have hStart : 0 < widthStart := (by positivity : (0:ℝ) < N^(-b)/2).trans_le hwidthStart
  have hReg : 0 < widthReg := (Real.rpow_pos_of_pos hNp _).trans_le hwidthReg
  have hcut0 : 0 < cut := (Real.rpow_pos_of_pos hNp _).trans_le hcut
  have hceil := (Nat.ceil_lt_add_one hX0).le
  have hH : (H:ℝ) ≤ 2*N^h := by dsimp only [H]; linarith only [hceil,hX1]
  have hcoarse : 6*(H:ℝ)/widthStart+2 ≤ N^(2*h+b) := by
    have hunit : 1 ≤ N^h*N^b := one_le_mul_of_one_le_of_one_le hX1 hb1
    have h26 : (26:ℝ) ≤ N^h := by norm_num at hlarge ⊢; linarith only [hlarge]
    calc
      _ ≤ 6*(2*N^h)/(N^(-b)/2)+2 := by gcongr
      _ = 24*(N^h*N^b)+2 := by rw [Real.rpow_neg hNp.le]; field_simp; ring
      _ ≤ 26*(N^h*N^b) := by linarith only [hunit]
      _ ≤ N^h*(N^h*N^b) := mul_le_mul_of_nonneg_right h26 (by positivity)
      _ = _ := by rw [←mul_assoc,←Real.rpow_add hNp,←Real.rpow_add hNp]; congr 1; ring
  have hpoly := derivative_poly_base (d := d) hlarge hd
  have hregPower : widthReg^(-epsilon) ≤ N^(E*epsilon) := by
    calc
      _ ≤ (N^(-E))^(-epsilon) := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos hNp _) hwidthReg (neg_nonpos.mpr hepsilon)
      _ = _ := by rw [←Real.rpow_mul hNp.le]; congr 1; ring
  have hfine : (2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
      ((151200*(12*(H:ℝ)+3)*N^h*(3:ℝ)^d)*widthReg^(-epsilon)/cut)*
        (2*(⌈2*(H:ℝ)+5⌉:ℝ)+1) ≤ N^(16*h+E*epsilon) := by
    calc
      _ = ((2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
          (151200*(12*(H:ℝ)+3)*N^h*(3:ℝ)^d)*(2*(⌈2*(H:ℝ)+5⌉:ℝ)+1))*
            widthReg^(-epsilon)/cut := by ring
      _ ≤ (N^h)^15*N^(E*epsilon)/N^(-h) := by gcongr
      _ = _ := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le,
          ←Real.rpow_add hNp,←Real.rpow_sub hNp]
        congr 1
        norm_num
        ring
  exact max_le
    (hcoarse.trans (Real.rpow_le_rpow_of_exponent_le hN hcoarseBudget))
    (hfine.trans (Real.rpow_le_rpow_of_exponent_le hN hfineBudget))

/-- The literal proposed P1 powers discharge every primitive
coefficient cap and derivative list, uniformly before all widths and
original data. The only inputs are fixed exponent comparisons. -/
theorem eventually_native_prestate_primitive_budgets
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {h areg E eta d : ℝ} (hh : 0 < h) (hA : 0 < areg) (hE : 0 < E)
    (heta : 0 < eta) (hd : d ≤ 1) (hsmall : h ≤ areg/100000000)
    (hfloorRange : 100000*h ≤ (areg/1000)*eta) :
    ∀ᶠ k in atTop, ∀ widthStart : ℝ,
      N k^(-(areg/1000))/2 ≤ widthStart → widthStart ≤ N k^(-(areg/1000)) →
      2*N k^h ≤ widthStart^(-eta) ∧
      Jets2.originalParameterCapConstant (N k^h) (4200*(12*N k^h+3)*N k^h) d ≤ widthStart^(-eta) ∧
      4*(4*N k^h+6)^3*(((12*N k^h+2)*N k^h)*N k^(100*h)) ≤ widthStart^(-eta) ∧
      ∀ widthReg cut : ℝ, N k^(-E) ≤ widthReg → N k^(-h) ≤ cut →
        let H := ⌈N k^h⌉₊
        max (6*(H:ℝ)/widthStart+2)
          ((2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
            ((151200*(12*(H:ℝ)+3)*N k^h*(3:ℝ)^d)*
              widthReg^(-(areg/(10000*E)))/cut)*(2*(⌈2*(H:ℝ)+5⌉:ℝ)+1)) ≤ N k^(areg/2) := by
  have hlarge := ((tendsto_rpow_atTop hh).comp hN).eventually
    (eventually_ge_atTop ((10:ℝ)^100))
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  change (10:ℝ)^100 ≤ N k^h at hc
  intro widthStart hstartLo hstartHi
  have hNp : 0 < N k := zero_lt_one.trans_le hk
  have hstart : 0 < widthStart :=
    (by positivity : (0:ℝ) < N k^(-(areg/1000))/2).trans_le hstartLo
  obtain ⟨hcoeff,hcap,hsupport⟩ := native_prestate_floor_budgets hk hh hc heta hstart hstartHi hd
    (by linarith only [hh,hfloorRange])
  refine ⟨hcoeff,hcap,hsupport,?_⟩
  intro widthReg cut hReg hCut
  apply native_prestate_derivative_list_bound hk hh
    (by positivity : 0 ≤ areg/1000) hc (by positivity : 0 ≤ areg/(10000*E))
    hstartLo hReg hCut hd
  · linarith only [hsmall,hA]
  · have heq : E*(areg/(10000*E))=areg/10000 := by field_simp
    rw [heq]
    linarith only [hsmall,hA]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
