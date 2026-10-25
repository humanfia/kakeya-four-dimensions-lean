-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.AlignedZoomCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/AlignedZoomCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/AlignedZoomCaps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/AlignedZoomCaps.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ZoomPriorCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicParameterBins

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory

noncomputable section

/-- Rounding a parameter width down by at most two costs at most eight
in the actual three-coordinate spatial exponent `2+d`, `0<=d<1`. -/
theorem rounded_spatial_ratio (q r w d : ℝ) (hq : 0 < q) (hr : 0 < r) (hw : 0 < w)
    (hrw : r / 2 ≤ w) (hd : 0 ≤ d) (hd1 : d < 1) :
    (q / w) ^ (2 + d) ≤ 8 * (q / r) ^ (2 + d) := by
  have hqr : q / w ≤ (2 * q) / r := (div_le_div_iff₀ hw hr).mpr (by nlinarith)
  have hqr' : q / w ≤ 2 * (q / r) := by convert hqr using 1 <;> ring
  have htwo : (2 : ℝ) ^ (2 + d) ≤ 8 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show 2 + d ≤ (3 : ℝ) by linarith)
    norm_num at h
    exact h
  calc
    _ ≤ (2 * (q / r)) ^ (2 + d) := Real.rpow_le_rpow (by positivity) hqr' (by linarith)
    _ = (2 : ℝ) ^ (2 + d) * (q / r) ^ (2 + d) := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (by positivity) _)

/-- Apply an ORIGINAL fine-bin mass floor inside the same original coarse
parameter world. The actual witness proves the whole-bin inclusion, and
dyadic alignment pays the bounded rounding loss in the spatial cap. -/
theorem aligned_original_zoom_conditional_cap {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (ρ r q K d : ℝ) (hρ : 0 < ρ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hq : 0 < q) (hK : 0 < K) (hd : 0 ≤ d) (hd1 : d < 1)
    (coarse fine : Fin 7 → ℤ) (center : Fin 7 → ℝ) (t a : ℝ) (b : Fin 2 → ℝ)
    (witness : Λ) (hcoarse : parameterCode ρ (c witness) = coarse)
    (hfine : zoomParameterPiece ρ c r witness = fine) (palette : ENNReal)
    (hcap : ν {l | zoomParameterPiece ρ c r l = fine ∧ (l, t) ∈ E ∧
      InCube (c l) t (zx center t + ρ * a)
        (fun i => zy center t i + ρ * b i) (ρ * q)} ≤
      ENNReal.ofReal (K * (ρ * q) ^ (2 + d)) * palette)
    (hfloor : ENNReal.ofReal
      ((ρ * dyadicParameterWidth (parameterLevel r)) ^ (2 + d) / K) * palette ≤
        ν {l | zoomParameterPiece ρ c r l = fine}) :
    let A := {l | parameterCode ρ (c l) = coarse}
    ((ν A)⁻¹ • ν.restrict A)
      {l | zoomParameterPiece ρ c r l = fine ∧ (l, t) ∈ E ∧
        InCube (zoomCoefficients ρ center (c l)) t a b q} ≤
      ENNReal.ofReal (8 * K ^ 2 * (q / r) ^ (2 + d)) *
        ((ν A)⁻¹ • ν.restrict A) {l | zoomParameterPiece ρ c r l = fine} := by
  let A := {l | parameterCode ρ (c l) = coarse}
  have hsub : {l | zoomParameterPiece ρ c r l = fine} ⊆ A :=
    original_parameter_fiber_subset c ρ hρ (parameterLevel r) coarse fine witness hcoarse hfine
  have h := original_zoom_conditional_cap ν A c E (zoomParameterPiece ρ c r) fine
    ρ (dyadicParameterWidth (parameterLevel r)) q K (2 + d) hρ (dyadicParameterWidth_pos _)
    hq hK center t a b palette hsub hcap hfloor
  have hratio := rounded_spatial_ratio q r (dyadicParameterWidth (parameterLevel r)) d hq hr
    (dyadicParameterWidth_pos _) (parameterLevel_width r hr hr1).1 hd hd1
  have hconstant : K ^ 2 * (q / dyadicParameterWidth (parameterLevel r)) ^ (2 + d) ≤
      8 * K ^ 2 * (q / r) ^ (2 + d) := by nlinarith [mul_le_mul_of_nonneg_left hratio (sq_nonneg K)]
  exact h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hconstant) le_rfl)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
