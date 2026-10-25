-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.RootGeometryBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SnapshotDyadicScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

/-- One polynomial coefficient pays every original support-grid and
native oscillation comparison. -/
def rootGeometryConstant (H B Lp : ℝ) : ℝ :=
  64*((3*H+1)*Lp+2*Lp+H+2)+16*(1+3*B)+16*H*Lp+1

/-- Three smallness comparisons suffice for all physical support-grid
and original incidence geometry. No measure or source occurs here. -/
theorem root_geometry_bounds {H B Lp b ρ ζ last resolution error : ℝ}
    (hH : 1 ≤ H) (hB : 1 ≤ B) (hLp : 0 ≤ Lp) (hb : 0 < b) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hlast : 0 < last) (hlastζ : last ≤ ζ) (hζ1 : ζ ≤ 1)
    (hresolution : 0 ≤ resolution) (hresb : resolution ≤ b) (herror : 0 ≤ error)
    (hCρ : rootGeometryConstant H B Lp*ρ ≤ last)
    (hCb : rootGeometryConstant H B Lp*b ≤ ρ*last)
    (hCe : 16*error ≤ ρ*last) :
    b ≤ ρ ∧ ρ ≤ last ∧
      (∀ w : ℝ, ρ*ζ/2 ≤ w →
        (1+3*B)*b ≤ w ∧ error*ρ ≤ w ∧ Lp*H*ρ^2 ≤ w ∧
          4*(2*((3*H+1)*Lp)*ρ+4*Lp*ρ)*ρ+(1+3*B)*b ≤ w/2) ∧
      (∀ r : ℝ, last ≤ r →
        (2+3*(H+1))*b ≤ ρ*r ∧ ρ ≤ r ∧
          (2*(error+2*(2*((3*H+1)*Lp)*ρ)*ρ)+2*(H+1)*b)/ρ ≤ r) ∧
      3*(H+1)*resolution ≤ ρ*last := by
  let C := rootGeometryConstant H B Lp
  let A := (3*H+1)*Lp
  have hH0 : 0 ≤ H := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hHL : 0 ≤ H*Lp := mul_nonneg hH0 hLp
  have hC1 : 1 ≤ C := by dsimp only [C,rootGeometryConstant]; nlinarith only [hH,hB,hLp,hHL]
  have hCA : 64*(A+2*Lp) ≤ C := by dsimp only [C,rootGeometryConstant,A]; nlinarith only [hH,hB,hLp,hHL]
  have hCB : 16*(1+3*B) ≤ C := by dsimp only [C,rootGeometryConstant,A]; nlinarith only [hH,hB,hLp,hHL]
  have hCH : 16*(3*H+5) ≤ C := by dsimp only [C,rootGeometryConstant,A]; nlinarith only [hH,hB,hLp,hHL]
  have hCHL : 16*H*Lp ≤ C := by dsimp only [C,rootGeometryConstant,A]; nlinarith only [hH,hB,hLp,hHL]
  have hρlast : ρ ≤ last := by nlinarith only [hC1,hCρ,hρ]
  have hlast1 : last ≤ 1 := hlastζ.trans hζ1
  have hbρ : b ≤ ρ := by nlinarith only [hC1,hCb,hb,hρ,hlast1]
  have hCρρ := mul_le_mul_of_nonneg_right hCρ hρ.le
  have hCAρ := mul_le_mul_of_nonneg_right hCA (sq_nonneg ρ)
  have hCBb := mul_le_mul_of_nonneg_right hCB hb.le
  have hCHb := mul_le_mul_of_nonneg_right hCH hb.le
  have hCHLρ := mul_le_mul_of_nonneg_right hCHL (sq_nonneg ρ)
  have hAρ : 8*A*ρ^2 ≤ ρ*last/8 := by
    nlinarith only [hCAρ,hCρρ,mul_nonneg hLp (sq_nonneg ρ)]
  have hLρ : (8*A+16*Lp)*ρ^2 ≤ ρ*last/8 := by nlinarith only [hCAρ,hCρρ]
  have hBb : (1+3*B)*b ≤ ρ*last/16 := by nlinarith only [hCBb,hCb]
  have hHb : (3*H+5)*b ≤ ρ*last/16 := by nlinarith only [hCHb,hCb]
  have hHLρ : H*Lp*ρ^2 ≤ ρ*last/16 := by nlinarith only [hCHLρ,hCρρ]
  have heρ : error*ρ ≤ ρ*last/16 := by
    nlinarith only [hCe,mul_le_of_le_one_right herror hρ1]
  have hρlastPos : 0 < ρ*last := mul_pos hρ hlast
  refine ⟨hbρ,hρlast,?_,?_,?_⟩
  · intro w hw
    have hρlastζ : ρ*last ≤ ρ*ζ := mul_le_mul_of_nonneg_left hlastζ hρ.le
    refine ⟨by nlinarith only [hBb,hρlastζ,hw,hρlastPos],
      by nlinarith only [heρ,hρlastζ,hw,hρlastPos],
      by nlinarith only [hHLρ,hρlastζ,hw,hρlastPos],?_⟩
    change 4*(2*A*ρ+4*Lp*ρ)*ρ+(1+3*B)*b ≤ w/2
    nlinarith only [hLρ,hBb,hρlastζ,hw,hρlastPos]
  · intro r hr
    have hρr : ρ*last ≤ ρ*r := mul_le_mul_of_nonneg_left hr hρ.le
    refine ⟨by nlinarith only [hHb,hρr,hρlastPos],hρlast.trans hr,?_⟩
    rw [div_le_iff₀ hρ]
    change 2*(error+2*(2*A*ρ)*ρ)+2*(H+1)*b ≤ r*ρ
    nlinarith only [hCe,hAρ,hHb,hρr,hρlastPos,
      mul_nonneg (by linarith : 0 ≤ H+3) hb.le]
  · have hh := mul_le_mul_of_nonneg_left hresb (by linarith : 0 ≤ 3*(H+1))
    nlinarith only [hh,hHb,hb,hρlastPos]

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
