-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalZoomSpatialCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalZoomSpatialCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalZoomSpatialCaps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalZoomSpatialCaps.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.AlignedZoomCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory

noncomputable section

/-- Construct BOTH spatial caps of the exact scalar-normal interface
from the ORIGINAL full-bin floors and the matching old palette numerators.
Only bins with an actual surviving incidence need a lower floor. -/
theorem original_zoom_spatial_caps {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (ρ K ζ d : ℝ) (hρ : 0 < ρ) (hK : 0 < K) (hζ : 0 < ζ)
    (hd : 0 ≤ d) (hd1 : d < 1)
    (coarse : Fin 7 → ℤ) (center : Fin 7 → ℝ)
    (hworld : ∀ l t, (l,t)∈E → parameterCode ρ (c l)=coarse)
    (hpositive : ν {l | parameterCode ρ (c l)=coarse} ≠ 0)
    (coarsePalette : ENNReal) (palette : ℝ → (Fin 7 → ℤ) → ENNReal)
    (hcoarseFloor : ENNReal.ofReal (ρ ^ (2+d)/K) * coarsePalette ≤
      ν {l | parameterCode ρ (c l)=coarse})
    (hcoarseCap : ∀ t a (b : Fin 2 → ℝ) q, ζ ≤ q → q ≤ 1 →
      ν {l | parameterCode ρ (c l)=coarse ∧ (l,t)∈E ∧
        InCube (c l) t (zx center t+ρ*a) (fun i => zy center t i+ρ*b i) (ρ*q)} ≤
          ENNReal.ofReal (K*(ρ*q)^(2+d))*coarsePalette)
    (hfineFloor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ l t, (l,t)∈E →
      ENNReal.ofReal ((ρ*dyadicParameterWidth (parameterLevel r))^(2+d)/K) *
        palette r (zoomParameterPiece ρ c r l) ≤
          ν {l' | zoomParameterPiece ρ c r l'=zoomParameterPiece ρ c r l})
    (hfineCap : ∀ r, ζ ≤ r → r ≤ 1 → ∀ fine t a (b : Fin 2 → ℝ) q,
      ζ ≤ q → q ≤ r →
      ν {l | zoomParameterPiece ρ c r l=fine ∧ (l,t)∈E ∧
        InCube (c l) t (zx center t+ρ*a) (fun i => zy center t i+ρ*b i) (ρ*q)} ≤
          ENNReal.ofReal (K*(ρ*q)^(2+d))*palette r fine) :
    let A := {l | parameterCode ρ (c l)=coarse}
    let νw := (ν A)⁻¹ • ν.restrict A
    (∀ t a (b : Fin 2 → ℝ) q, ζ ≤ q → q ≤ 1 →
      νw {l | (l,t)∈E ∧ InCube (zoomCoefficients ρ center (c l)) t a b q} ≤
        ENNReal.ofReal (8*K^2*q^(2+d))) ∧
    (∀ r, ζ ≤ r → r ≤ 1 → ∀ fine t a (b : Fin 2 → ℝ) q, ζ ≤ q → q ≤ r →
      νw {l | zoomParameterPiece ρ c r l=fine ∧ (l,t)∈E ∧
        InCube (zoomCoefficients ρ center (c l)) t a b q} ≤
          ENNReal.ofReal (8*K^2*(q/r)^(2+d))*νw {l | zoomParameterPiece ρ c r l=fine}) := by
  let A := {l | parameterCode ρ (c l)=coarse}
  let νw := (ν A)⁻¹ • ν.restrict A
  constructor
  · intro t a b q hq hq1
    have hq0 := hζ.trans_le hq
    let H := {l | (l,t)∈E ∧ InCube (zoomCoefficients ρ center (c l)) t a b q}
    have hHA : H ⊆ A := fun l hl => hworld l t hl.1
    have hnum : ν H ≤ ENNReal.ofReal (K*(ρ*q)^(2+d))*coarsePalette := by
      have heq : H = {l | parameterCode ρ (c l)=coarse ∧ (l,t)∈E ∧
          InCube (c l) t (zx center t+ρ*a) (fun i => zy center t i+ρ*b i) (ρ*q)} := by
        ext l
        simp only [H,mem_ofPred_eq,inCube_zoom_iff ρ hρ]
        constructor
        · exact fun h => ⟨hworld l t h.1,h⟩
        · exact fun h => h.2
      rw [heq]
      exact hcoarseCap t a b q hq hq1
    have hratio := original_zoom_mass_ratio ρ 1 q K (2+d) hρ zero_lt_one hq0 hK
      (ν H) (ν A) coarsePalette hnum (by simpa only [mul_one] using hcoarseFloor)
    simp only [div_one] at hratio
    have hnormalized : νw H ≤ ENNReal.ofReal (K^2*q^(2+d)) := by
      calc
        _ = (ν A)⁻¹ * ν H := by
          change ((ν A)⁻¹ • ν.restrict A) H = _
          rw [Measure.smul_apply,smul_eq_mul,Measure.restrict_eq_self ν hHA]
        _ ≤ (ν A)⁻¹ * (ENNReal.ofReal (K^2*q^(2+d))*ν A) := mul_le_mul' le_rfl hratio
        _ = _ := by
          rw [mul_comm (ENNReal.ofReal _),← mul_assoc,
            ENNReal.inv_mul_cancel hpositive (measure_ne_top _ _),one_mul]
    apply hnormalized.trans
    apply ENNReal.ofReal_le_ofReal
    have hh : 0 ≤ K^2*q^(2+d) := by positivity
    nlinarith
  · intro r hr hr1 fine t a b q hq hqr
    by_cases hex : ∃ l, zoomParameterPiece ρ c r l=fine ∧ (l,t)∈E ∧
        InCube (zoomCoefficients ρ center (c l)) t a b q
    · obtain ⟨l,hl,hlE,hlcube⟩ := hex
      have hfloor := hfineFloor r hr hr1 l t hlE
      rw [hl] at hfloor
      exact aligned_original_zoom_conditional_cap ν c E ρ r q K d hρ (hζ.trans_le hr) hr1
        (hζ.trans_le hq) hK hd hd1 coarse fine center t a b l (hworld l t hlE) hl
        (palette r fine) (hfineCap r hr hr1 fine t a b q hq hqr) hfloor
    · have hempty : {l | zoomParameterPiece ρ c r l=fine ∧ (l,t)∈E ∧
          InCube (zoomCoefficients ρ center (c l)) t a b q} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro l hl
        exact hex ⟨l,hl⟩
      rw [hempty,measure_empty]
      exact bot_le

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
