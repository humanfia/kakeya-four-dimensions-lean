-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.DyadicParameterPaletteCoarsening, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/DyadicParameterPaletteCoarsening.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 9990050b5ef6bdaa550836abbcdb33eb4643e8c9,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/DyadicParameterPaletteCoarsening.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicParameterBins

/-! # Exact velocity-header nesting for dyadic parameter grids -/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
noncomputable section

def dyadicPaletteParent {n : ℕ} (level : ℕ) (q : Fin n → ℤ) : Fin n → ℤ :=
  fun i => q i/(2:ℤ)^level

theorem dyadicPaletteParent_parameterCode {n : ℕ} (level : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) (v : Fin n → ℝ) :
    dyadicPaletteParent level (parameterCode (ρ*dyadicParameterWidth level) v)=parameterCode ρ v := by
  funext i
  change ⌊v i/(ρ*dyadicParameterWidth level)⌋/(2:ℤ)^level=⌊v i/ρ⌋
  have heq : v i/(ρ*dyadicParameterWidth level)=(v i/ρ)*(((2:ℤ)^level : ℤ) : ℝ) := by
    simp only [dyadicParameterWidth,Int.cast_pow,Int.cast_ofNat]
    field_simp
  rw [heq]
  exact Int.mul_cast_floor_div_cancel_of_pos (by positivity : (0:ℤ)<2^level) (v i/ρ)

theorem dyadicPaletteParent_velocity_header (level : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (c : Fin 7 → ℝ) :
    dyadicPaletteParent level (parameterCode (ρ*dyadicParameterWidth level) (zv c))=
      ![parameterCode ρ c 4,parameterCode ρ c 6] := by
  rw [dyadicPaletteParent_parameterCode level hρ]
  funext i
  fin_cases i <;> rfl

theorem measurable_dyadicPaletteParent {n : ℕ} (level : ℕ) :
    Measurable (dyadicPaletteParent (n := n) level) := measurable_of_countable _

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
