-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalScalarNormalWorld, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalScalarNormalWorld.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalScalarNormalWorld.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalScalarNormalWorld.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomSpatialCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CanonicalParameterWorlds
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Restrict
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalCoarsePalette

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

/-- Assemble the EXACT j2 scalar-normal interface in one ORIGINAL full
parameter world. The prior is its full original conditional law, while
all labels may have undergone the preceding incidence restrictions.
Actual SS/row/residual estimates and ORIGINAL full-bin floors/numerators
supply every field; no scalar-normal statement is assumed. -/
theorem original_scalar_normal_world {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E) (F : ℝ → Fin 2 → ℝ) (hFm : Measurable F)
    (ρ ζ d H Kcap Kss Krc Kres : ℝ) (hρ : 0 < ρ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hd : 0 ≤ d) (hd1 : d < 1) (hH : 1 ≤ H) (hKcap : 0 < Kcap)
    (hcapH : 8*Kcap^2 ≤ H) (hssH : Kss ≤ H) (hrc0 : 0 ≤ Krc) (hrcH : Krc ≤ H)
    (hresH : Kres ≤ H) (hρζ : ρ ≤ ζ)
    (coarse : Fin 7 → ℤ)
    (hworld : ∀ l t, (l,t)∈E → parameterCode ρ (c l)=coarse)
    (hpositive : ν {l | parameterCode ρ (c l)=coarse} ≠ 0)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (hrow : ∀ z∈E, ‖F z.2‖ ≤ H)
    (hdense : ENNReal.ofReal H⁻¹ ≤
      (((ν {l | parameterCode ρ (c l)=coarse})⁻¹ •
        ν.restrict {l | parameterCode ρ (c l)=coarse}).prod volume) E)
    (hSS : ∀ t, IntervalAD ζ d Kss
      {x | ∃ l, (l,t)∈E ∧ zS F (zoomCoefficients ρ (parameterCenter ρ coarse) (c l)) t=x})
    (hRC : ∀ z∈E, ∀ z'∈E, ‖F z.2-F z'.2‖ ≤ Krc*(|z.2-z'.2|+ρ))
    (hResC : ∀ z∈E, ∀ z'∈E,
      |zR F (zoomCoefficients ρ (parameterCenter ρ coarse) (c z.1)) z.2-
        zR F (zoomCoefficients ρ (parameterCenter ρ coarse) (c z'.1)) z'.2| ≤
          Kres*(‖zpos (zoomCoefficients ρ (parameterCenter ρ coarse) (c z.1)) z.2-
            zpos (zoomCoefficients ρ (parameterCenter ρ coarse) (c z'.1)) z'.2‖+ζ))
    (coarsePalette : ENNReal) (palette : ℝ → (Fin 7 → ℤ) → ENNReal)
    (hcoarseFloor : ENNReal.ofReal (ρ^(2+d)/Kcap)*coarsePalette ≤
      ν {l | parameterCode ρ (c l)=coarse})
    (hcoarseCap : ∀ t a (b : Fin 2 → ℝ) q, ζ ≤ q → q ≤ 1 →
      ν {l | parameterCode ρ (c l)=coarse ∧ (l,t)∈E ∧
        InCube (c l) t (zx (parameterCenter ρ coarse) t+ρ*a)
          (fun i => zy (parameterCenter ρ coarse) t i+ρ*b i) (ρ*q)} ≤
            ENNReal.ofReal (Kcap*(ρ*q)^(2+d))*coarsePalette)
    (hfineFloor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ l t, (l,t)∈E →
      ENNReal.ofReal ((ρ*dyadicParameterWidth (parameterLevel r))^(2+d)/Kcap) *
        palette r (zoomParameterPiece ρ c r l) ≤
          ν {l' | zoomParameterPiece ρ c r l'=zoomParameterPiece ρ c r l})
    (hfineCap : ∀ r, ζ ≤ r → r ≤ 1 → ∀ fine t a (b : Fin 2 → ℝ) q,
      ζ ≤ q → q ≤ r →
      ν {l | zoomParameterPiece ρ c r l=fine ∧ (l,t)∈E ∧
        InCube (c l) t (zx (parameterCenter ρ coarse) t+ρ*a)
          (fun i => zy (parameterCenter ρ coarse) t i+ρ*b i) (ρ*q)} ≤
            ENNReal.ofReal (Kcap*(ρ*q)^(2+d))*palette r fine) :
    ScalarNormal
      ((ν {l | parameterCode ρ (c l)=coarse})⁻¹ • ν.restrict {l | parameterCode ρ (c l)=coarse})
      (fun l => zoomCoefficients ρ (parameterCenter ρ coarse) (c l)) E F
      (zoomParameterPiece ρ c) H ζ d := by
  let A := {l | parameterCode ρ (c l)=coarse}
  let νw := (ν A)⁻¹ • ν.restrict A
  have hcaps := original_zoom_spatial_caps ν c E ρ Kcap ζ d hρ hKcap hζ hd hd1 coarse
    (parameterCenter ρ coarse) hworld hpositive coarsePalette palette
    hcoarseFloor hcoarseCap hfineFloor hfineCap
  refine {
    prob := Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.originalCoarsePalette_probability ν A hpositive (measure_ne_top _ _)
    one_le_K := hH
    zeta_pos := hζ
    zeta_le_one := hζ1
    measurable_c := measurable_zoomCoefficients ρ _ hc
    measurableSet_E := hE
    measurable_F := hFm
    measurable_piece := fun r => measurable_zoomParameterPiece ρ hc r
    time_mem := ht
    coeff_le := ?_
    row_le := hrow
    dense := hdense
    support := fun t => intervalAD_mono_const hζ (hSS t) hssH
    abs_cap := ?_
    row_cmp := ?_
    resid_cmp := ?_
    piece_diam := ?_
    bin_cap := ?_ }
  · intro z hz i
    have hh := (original_parameter_zoom_coefficients_bound ρ hρ (c z.1) i).trans hH
    simpa only [hworld z.1 z.2 hz] using hh
  · intro t a b q hq hq1
    exact (hcaps.1 t a b q hq hq1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcapH (Real.rpow_nonneg (hζ.trans_le hq).le _)))
  · intro z hz z' hz'
    exact (hRC z hz z' hz').trans (mul_le_mul hrcH
      (add_le_add le_rfl hρζ) (by positivity) (by linarith))
  · intro z hz z' hz'
    exact (hResC z hz z' hz').trans
      (mul_le_mul_of_nonneg_right hresH (by positivity))
  · intro r hr hr1 l l' hh
    exact zoomParameterPiece_diameter ρ hρ c (parameterCenter ρ coarse) r (hζ.trans_le hr) hr1 hh
  · intro r hr hr1 fine t a b q hq hqr
    exact (hcaps.2 r hr hr1 fine t a b q hq hqr).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcapH (Real.rpow_nonneg
        (div_nonneg (hζ.trans_le hq).le (hζ.trans_le hr).le) _))) le_rfl)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
