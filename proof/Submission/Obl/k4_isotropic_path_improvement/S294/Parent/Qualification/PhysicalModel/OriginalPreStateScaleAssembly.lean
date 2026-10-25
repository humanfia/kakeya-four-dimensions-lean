-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalPreStateScaleAssembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalPreStateScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Jets2

noncomputable section

/-- The original polynomial mesh is fine enough for the actual
integer-rounded derivative coefficient bound. -/
theorem rounded_coefficient_mesh_small {N h E target b : ℝ}
    (hN : 1 < N) (hlarge : 32 ≤ N^h) (hroom : E+2*h ≤ target)
    (hb : 0 ≤ b) (hbBound : b ≤ N^(-target)) :
    3*((⌈N^h⌉₊:ℝ)+1)*b ≤ N^(-E) := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le h)).le
  have hcoeff : 3*((⌈N^h⌉₊:ℝ)+1) ≤ (N^h)^2 := by nlinarith only [hceil,hlarge]
  calc
    _ ≤ (N^h)^2*N^(-target) := mul_le_mul hcoeff hbBound hb (by positivity)
    _ = N^(2*h-target) := by
      rw [←Real.rpow_mul_natCast hNp.le,←Real.rpow_add hNp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith only [hroom])

/-- The exact scalar P1 record at its explicit powers. All its
original floors and derivative tables are still constructed later. -/
def originalPreStateScales_of_power_budgets
    (s : OriginalRootScales) (N h a E target : ℝ)
    (hN : 1 < N) (hh : 0 < h) (ha : 0 < a) (hE : 0 < E)
    (hdim : s.dimension < 1)
    (hH : s.H=N^h) (hCpure : s.Cpure=N^h) (hKL : s.KL=N^(a/2))
    (hexponent : s.floorExponent=a/(10000*E))
    (hcount : 0 < s.floorCount)
    (hfinest : s.floorStart+s.floorCount-1=s.paletteFinest)
    (hresolved : s.b ≤ dyadicParameterWidth s.paletteFinest)
    (hfloor : N^(-E) ≤ dyadicParameterWidth s.paletteFinest)
    (hmesh : s.b ≤ N^(-target)) (hroom : E+2*h ≤ target) (hlarge : 32 ≤ N^h)
    (hstart : dyadicParameterWidth s.floorStart ≤
      originalPreStateWidth s.dimension s.floorExponent s.regLength)
    (hcoeffBudget : 2*N^h ≤ (dyadicParameterWidth s.floorStart)^
      (-originalPreStateEta s.dimension s.floorExponent s.regLength))
    (hcapBudget : originalParameterCapConstant (N^h) (4200*(12*N^h+3)*N^h) s.dimension ≤
      (dyadicParameterWidth s.floorStart)^(-originalPreStateEta s.dimension s.floorExponent s.regLength))
    (hsupportBudget : 4*(4*N^h+6)^3*(((12*N^h+2)*N^h)*N^(100*h)) ≤
      (dyadicParameterWidth s.floorStart)^(-originalPreStateEta s.dimension s.floorExponent s.regLength))
    (hlist : ∀ w : ℝ, N^(-E) ≤ w →
      let H := ⌈N^h⌉₊
      max (6*(H:ℝ)/dyadicParameterWidth s.floorStart+2)
        ((2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
          ((151200*(12*(H:ℝ)+3)*N^h*(3:ℝ)^s.dimension)*
            w^(-(a/(10000*E)))/N^(-h))*(2*(⌈2*(H:ℝ)+5⌉:ℝ)+1)) ≤ N^(a/2)) :
    OriginalPreStateScales s := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hresb : s.resolution ≤ s.b := by
    rw [s.hb_eq]
    exact le_mul_of_one_le_right s.hresolution.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hregFloor (i : Fin s.regLength) : N^(-E) ≤ dyadicParameterWidth (s.regLevel i.val) :=
    hfloor.trans (dyadicParameterWidth_antitone (s.hregFinest i.val i.isLt))
  have hsmall0 := rounded_coefficient_mesh_small hN hlarge hroom s.hb.le hmesh
  exact {
    hdimension := hdim
    hexponent := by rw [hexponent]; positivity
    hcount := hcount
    hstart := hstart
    Kfloor := N^(100*h)
    hKfloor := Real.rpow_pos_of_pos hNp _
    hresolved := by simpa only [hfinest] using hresolved
    hcoeffBudget := by simpa only [hH] using hcoeffBudget
    hcapBudget := by simpa only [hH,hCpure] using hcapBudget
    hsupportBudget := by simpa only [hH,hCpure] using hsupportBudget
    Hnat := ⌈N^h⌉₊
    hHnat := by rw [hH]; exact Nat.le_ceil _
    hregEnd := fun i => by
      have hf := hfinest
      have hc := hcount
      have hr := s.hregFinest i.val i.isLt
      omega
    cut := fun _ => N^(-h)
    hcut := fun _ => Real.rpow_pos_of_pos hNp _
    hsmall := fun i => (mul_le_mul_of_nonneg_left hresb (by positivity)).trans
      (hsmall0.trans (hregFloor i))
    hKL := fun i => by
      simpa only [hCpure,hexponent,hKL] using hlist _ (hregFloor i)
    hfloorFinest := hfinest.le
  }

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
