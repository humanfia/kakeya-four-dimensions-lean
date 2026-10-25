-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CurrentEntryScalarNormalWorld, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/CurrentEntryScalarNormalWorld.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CurrentEntrySpatialCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalScalarNormalWorld

/-! # Scalar-normal worlds using the prepared current-incidence spatial caps

The preceding preparation supplies both spatial numerator families on
R. They survive every later selected world S. The profile amplitude is
absorbed into the reference weights and cancels from the normalized
spatial bounds, so no amplitude or inverse amplitude is paid in H.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped ENNReal
noncomputable section

/-- Use the output of `prepare_original_spatial_cap_source` on any
later original world. Every scalar-normal spatial clause is derived;
only original full-bin floors remain in the denominator. -/
theorem original_scalar_normal_world_of_prepared_incidence_caps
    {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (R S : Set (Λ×ℝ)) (hS : MeasurableSet S) (hSR : S⊆R)
    (F : ℝ → Fin 2 → ℝ) (hFm : Measurable F)
    (ρ ζ d H Kcap Knum Kss Krc Kres amplitude : ℝ)
    (hρ : 0 < ρ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : 0 ≤ d) (hd1 : d < 1)
    (hH : 1 ≤ H) (hKcap : 0 < Kcap) (hnumBudget : Knum ≤ Kcap) (hamp : 0 ≤ amplitude)
    (hcapH : 8*Kcap^2 ≤ H) (hssH : Kss ≤ H) (hrc0 : 0 ≤ Krc) (hrcH : Krc ≤ H)
    (hresH : Kres ≤ H) (hρζ : ρ ≤ ζ) (world : Fin 7 → ℤ)
    (hworld : ∀ l t, (l,t)∈S → parameterCode ρ (c l)=world)
    (hpositive : ν {l | parameterCode ρ (c l)=world} ≠ 0)
    (ht : ∀ z∈S, z.2∈Icc (0:ℝ) 1)
    (hrow : ∀ z∈S, ‖F z.2‖ ≤ H)
    (hdense : ENNReal.ofReal H⁻¹ ≤
      (((ν {l | parameterCode ρ (c l)=world})⁻¹ •
        ν.restrict {l | parameterCode ρ (c l)=world}).prod volume) S)
    (hSS : ∀ t, IntervalAD ζ d Kss
      {x | ∃ l, (l,t)∈S ∧ zS F (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t=x})
    (hRC : ∀ z∈S, ∀ z'∈S, ‖F z.2-F z'.2‖ ≤ Krc*(|z.2-z'.2|+ρ))
    (hResC : ∀ z∈S, ∀ z'∈S,
      |zR F (zoomCoefficients ρ (parameterCenter ρ world) (c z.1)) z.2-
        zR F (zoomCoefficients ρ (parameterCenter ρ world) (c z'.1)) z'.2| ≤
      Kres*(‖zpos (zoomCoefficients ρ (parameterCenter ρ world) (c z.1)) z.2-
        zpos (zoomCoefficients ρ (parameterCenter ρ world) (c z'.1)) z'.2‖+ζ))
    (coarseWeight : ℝ≥0∞) (fineWeight : ℝ → (Fin 7 → ℤ) → ℝ≥0∞)
    (hcoarseFloor : ENNReal.ofReal ((ρ^((2:ℝ)+d)/Kcap)*amplitude)*coarseWeight ≤
      ν {l | parameterCode ρ (c l)=world})
    (hfineFloor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ l t, (l,t)∈S →
      ENNReal.ofReal (((ρ*dyadicParameterWidth (parameterLevel r))^((2:ℝ)+d)/Kcap)*amplitude)*
        fineWeight r (zoomParameterPiece ρ c r l) ≤
        ν {l' | zoomParameterPiece ρ c r l'=zoomParameterPiece ρ c r l})
    (hcoarseR : ∀ (t a : ℝ) (b : Fin 2 → ℝ) (q : ℝ), ζ ≤ q → q ≤ 1 →
      ν {l | parameterCode ρ (c l)=world ∧ (l,t)∈R ∧
        InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
        ENNReal.ofReal (Knum*(ρ*q)^((2:ℝ)+d)*amplitude)*coarseWeight)
    (hfineR : ∀ r, ζ ≤ r → r ≤ 1 → ∀ fine (t a : ℝ) (b : Fin 2 → ℝ) q, ζ ≤ q → q ≤ r →
      ν {l | parameterCode ρ (c l)=world ∧ zoomParameterPiece ρ c r l=fine ∧ (l,t)∈R ∧
        InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
        ENNReal.ofReal (Knum*(ρ*q)^((2:ℝ)+d)*amplitude)*fineWeight r fine) :
    ScalarNormal
      ((ν {l | parameterCode ρ (c l)=world})⁻¹ • ν.restrict {l | parameterCode ρ (c l)=world})
      (fun l => zoomCoefficients ρ (parameterCenter ρ world) (c l)) S F
      (zoomParameterPiece ρ c) H ζ d := by
  have hfactor (x : ℝ) (weight : ℝ≥0∞) : ENNReal.ofReal (x*amplitude)*weight=
      ENNReal.ofReal x*(ENNReal.ofReal amplitude*weight) := by
    rw [mul_comm x amplitude,ENNReal.ofReal_mul hamp]
    ring
  refine original_scalar_normal_world ν c hc S hS F hFm ρ ζ d H Kcap Kss Krc Kres
    hρ hζ hζ1 hd hd1 hH hKcap hcapH hssH hrc0 hrcH hresH hρζ world
    hworld hpositive ht hrow hdense hSS hRC hResC
    (ENNReal.ofReal amplitude*coarseWeight)
    (fun r fine => ENNReal.ofReal amplitude*fineWeight r fine) ?_ ?_ ?_ ?_
  · simpa only [hfactor] using hcoarseFloor
  · intro t a b q hq hq1
    have hn := (measure_mono (show {l | parameterCode ρ (c l)=world ∧ (l,t)∈S ∧
        InCube (c l) t (zx (parameterCenter ρ world) t+ρ*a)
          (fun i => zy (parameterCenter ρ world) t i+ρ*b i) (ρ*q)} ⊆
        {l | parameterCode ρ (c l)=world ∧ (l,t)∈R ∧
          InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} from by
      rintro l ⟨hl,hs,hcube⟩
      exact ⟨hl,hSR hs,(inCube_zoom_iff ρ hρ _ _ t a b q).mpr hcube⟩)).trans
        (hcoarseR t a b q hq hq1)
    rw [hfactor] at hn
    exact hn.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hnumBudget (Real.rpow_nonneg (mul_nonneg hρ.le (hζ.trans_le hq).le) _))) le_rfl)
  · intro r hr hr1 l t hl
    simpa only [hfactor] using hfineFloor r hr hr1 l t hl
  · intro r hr hr1 fine t a b q hq hqr
    have hn := (measure_mono (show {l | zoomParameterPiece ρ c r l=fine ∧ (l,t)∈S ∧
        InCube (c l) t (zx (parameterCenter ρ world) t+ρ*a)
          (fun i => zy (parameterCenter ρ world) t i+ρ*b i) (ρ*q)} ⊆
        {l | parameterCode ρ (c l)=world ∧ zoomParameterPiece ρ c r l=fine ∧ (l,t)∈R ∧
          InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} from by
      rintro l ⟨hl,hs,hcube⟩
      exact ⟨hworld l t hs,hl,hSR hs,(inCube_zoom_iff ρ hρ _ _ t a b q).mpr hcube⟩)).trans
        (hfineR r hr hr1 fine t a b q hq hqr)
    rw [hfactor] at hn
    exact hn.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hnumBudget (Real.rpow_nonneg (mul_nonneg hρ.le (hζ.trans_le hq).le) _))) le_rfl)

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
