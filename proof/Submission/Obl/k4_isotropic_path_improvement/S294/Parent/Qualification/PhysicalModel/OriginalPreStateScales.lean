-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalPreStateScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorPreStateSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootCosts

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The floor exponent budget chosen before every datum, at the fixed
number of regularity snapshots. -/
def originalPreStateEta (dimension epsilon : ℝ) (length : ℕ) : ℝ :=
  if h : 0 ≤ dimension ∧ dimension < 1 ∧ 0 < epsilon then
    Classical.choose (NativeAncestor.prepare_native_original_pre_state_data
      (I:=Fin length) dimension epsilon h.1 h.2.1 h.2.2)
  else 1

/-- The corresponding pre-data upper floor width. -/
def originalPreStateWidth (dimension epsilon : ℝ) (length : ℕ) : ℝ :=
  if h : 0 ≤ dimension ∧ dimension < 1 ∧ 0 < epsilon then
    Classical.choose (Classical.choose_spec (NativeAncestor.prepare_native_original_pre_state_data
      (I:=Fin length) dimension epsilon h.1 h.2.1 h.2.2)).2
  else 1

theorem originalPreStateEta_pos (dimension epsilon : ℝ) (length : ℕ) :
    0 < originalPreStateEta dimension epsilon length := by
  unfold originalPreStateEta
  split_ifs with h
  · exact (Classical.choose_spec (NativeAncestor.prepare_native_original_pre_state_data
      (I:=Fin length) dimension epsilon h.1 h.2.1 h.2.2)).1
  · exact zero_lt_one

theorem originalPreStateWidth_pos (dimension epsilon : ℝ) (length : ℕ) :
    0 < originalPreStateWidth dimension epsilon length := by
  unfold originalPreStateWidth
  split_ifs with h
  · exact (Classical.choose_spec (Classical.choose_spec
      (NativeAncestor.prepare_native_original_pre_state_data
        (I:=Fin length) dimension epsilon h.1 h.2.1 h.2.2)).2).1
  · exact zero_lt_one

/-- All additional P1 requirements are scalar inequalities. The rows,
source, full prior, palette and derivative tables are constructed later. -/
structure OriginalPreStateScales (s : OriginalRootScales) where
  hdimension : s.dimension < 1
  hexponent : 0 < s.floorExponent
  hcount : 0 < s.floorCount
  hstart : Jets2.dyadicParameterWidth s.floorStart ≤
    originalPreStateWidth s.dimension s.floorExponent s.regLength
  Kfloor : ℝ
  hKfloor : 0 < Kfloor
  hresolved : s.b ≤ Jets2.dyadicParameterWidth (s.floorStart+s.floorCount-1)
  hcoeffBudget : 2*s.H ≤ (Jets2.dyadicParameterWidth s.floorStart)^
    (-originalPreStateEta s.dimension s.floorExponent s.regLength)
  hcapBudget : Jets2.originalParameterCapConstant s.H (4200*(12*s.H+3)*s.Cpure) s.dimension ≤
    (Jets2.dyadicParameterWidth s.floorStart)^(-originalPreStateEta s.dimension s.floorExponent s.regLength)
  hsupportBudget : 4*(4*s.H+6)^3*(((12*s.H+2)*s.Cpure)*Kfloor) ≤
    (Jets2.dyadicParameterWidth s.floorStart)^(-originalPreStateEta s.dimension s.floorExponent s.regLength)
  Hnat : ℕ
  hHnat : s.H ≤ (Hnat:ℝ)
  hregEnd : ∀ i : Fin s.regLength, s.regLevel i.val < s.floorStart+s.floorCount
  cut : Fin s.regLength → ℝ
  hcut : ∀ i, 0 < cut i
  hsmall : ∀ i : Fin s.regLength, 3*((Hnat:ℝ)+1)*s.resolution ≤
    Jets2.dyadicParameterWidth (s.regLevel i.val)
  hKL : ∀ i : Fin s.regLength, max (6*(Hnat:ℝ)/Jets2.dyadicParameterWidth s.floorStart+2)
    ((2*(Hnat:ℝ)+3)^7*(6*(Hnat:ℝ)+12)^4*
      ((151200*(12*(Hnat:ℝ)+3)*s.Cpure*(3:ℝ)^s.dimension)*
        (Jets2.dyadicParameterWidth (s.regLevel i.val))^(-s.floorExponent)/cut i)*
          (2*(⌈2*(Hnat:ℝ)+5⌉:ℝ)+1)) ≤ s.KL
  hfloorFinest : s.floorStart+s.floorCount-1 ≤ s.paletteFinest

/-- A uniform charge for both original pre-state cuts. -/
def OriginalPreStateScales.charge {s : OriginalRootScales} (v : OriginalPreStateScales s) : ENNReal :=
  ENNReal.ofReal ((s.Kcensus^2*((2:ℝ)^s.steps)^3)*(s.floorCount:ℝ)/v.Kfloor)+
    ENNReal.ofReal s.H⁻¹+
    ENNReal.ofReal (((4*s.H+2)^2)*(Jets2.dyadicParameterWidth s.floorStart)^
      (originalPreStateEta s.dimension s.floorExponent s.regLength)/
        (1-(2:ℝ)^(-originalPreStateEta s.dimension s.floorExponent s.regLength)))+
    ∑ i : {i : Fin s.regLength // s.floorStart ≤ s.regLevel i.val},
      ENNReal.ofReal (v.cut i.val*Jets2.zoomBlockVisitConstant)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
