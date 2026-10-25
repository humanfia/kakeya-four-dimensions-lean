-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PencilRadiusScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

/-- A single concrete original-velocity pencil radius works for both
row breadth and world support. -/
noncomputable def originalPencilRadius (H width : ℝ) : ℝ :=
  min (1/(8*(H+1))) (width/(8*(H+1)^2))

/-- All pencil width, positivity and original polynomial lower-floor
conditions for the concrete radius. -/
theorem originalPencilRadius_bounds {H width : ℝ} (hH : 32 ≤ H)
    (hwidth : H⁻¹ ≤ width) :
    let radius := originalPencilRadius H width
    0 < radius ∧ radius ≤ 1/4 ∧
      2*(H+1)*radius ≤ width ∧
      2*(H+1)*((H+1)*radius) ≤ width ∧
      (H+1)*radius ≤ 1/4 ∧
      (H^4)⁻¹ ≤ radius := by
  intro radius
  have hHpos : 0<H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hHp : 0<H+1 := by linarith
  have hwpos : 0<width := (inv_pos.mpr hHpos).trans_le hwidth
  have hrpos : 0<radius := lt_min (by positivity) (by positivity)
  have hfirst : radius ≤ 1/(8*(H+1)) := min_le_left _ _
  have hsecond : radius ≤ width/(8*(H+1)^2) := min_le_right _ _
  have hfirst' := (le_div_iff₀ (by positivity : 0<8*(H+1))).mp hfirst
  have hsecond' := (le_div_iff₀ (by positivity : 0<8*(H+1)^2)).mp hsecond
  have hpencil : 2*(H+1)*((H+1)*radius) ≤ width := by
    nlinarith only [hsecond',hwpos]
  have hbroad : 2*(H+1)*radius ≤ width := by
    have hh := mul_le_mul_of_nonneg_right hH1 (mul_nonneg (by linarith : 0 ≤ H+1) hrpos.le)
    nlinarith only [hpencil,hh,mul_nonneg hHp.le hrpos.le]
  have hrsmall : (H+1)*radius ≤ 1/4 := by nlinarith only [hfirst']
  have hrsmall' : radius ≤ 1/4 := by nlinarith only [hrsmall,hH1,hrpos]
  have hcube : 8*(H+1)^2 ≤ H^3 := by
    calc
      _ ≤ 8*(2*H)^2 := by gcongr; linarith
      _ = 32*H^2 := by ring
      _ ≤ H*H^2 := mul_le_mul_of_nonneg_right hH (sq_nonneg H)
      _ = _ := by ring
  have hfour : 8*(H+1) ≤ H^4 := by
    calc
      _ ≤ 8*(H+1)^2 := by nlinarith only [hH1]
      _ ≤ H^3 := hcube
      _ ≤ H^4 := pow_le_pow_right₀ hH1 (by decide : 3 ≤ 4)
  have hrLower : (H^4)⁻¹ ≤ radius := by
    apply le_min
    · simpa only [one_div] using
        one_div_le_one_div_of_le (by positivity : 0<8*(H+1)) hfour
    · calc
        (H^4)⁻¹=H⁻¹/H^3 := by field_simp <;> ring
        _ ≤ H⁻¹/(8*(H+1)^2) :=
          div_le_div_of_nonneg_left (inv_nonneg.mpr hHpos.le) (by positivity) hcube
        _ ≤ width/(8*(H+1)^2) := div_le_div_of_nonneg_right hwidth (by positivity)
  exact ⟨hrpos,hrsmall',hbroad,hpencil,hrsmall,hrLower⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
