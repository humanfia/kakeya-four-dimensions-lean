-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PreparedWorldBuilder, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/Qualification/PreparedWorldBuilder.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CurrentEntryScalarNormalWorld

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped ENNReal

noncomputable section

/-- The original spatial preparation and hereditary support/row/residual
estimates construct the scalar-normal builder used by total-world
qualification. Full-bin floors are required only on the actual source;
density is tested only for the later failed restriction. No positive
density assumption is made on every coefficient world. -/
theorem original_scalar_normal_builder_of_prepared_incidence_caps
    {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (R E : Set (Λ×ℝ)) (hER : E⊆R)
    (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ) (hFm : ∀ q, Measurable (F q))
    (ρ ζ d H Kcap Knum Kss Krc Kres amplitude : ℝ)
    (hρ : 0 < ρ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : 0 ≤ d) (hd1 : d < 1)
    (hH : 1 ≤ H) (hKcap : 0 < Kcap) (hnumBudget : Knum ≤ Kcap) (hamp : 0 ≤ amplitude)
    (hcapH : 8*Kcap^2 ≤ H) (hssH : Kss ≤ H) (hrc0 : 0 ≤ Krc) (hrcH : Krc ≤ H)
    (hresH : Kres ≤ H) (hρζ : ρ ≤ ζ)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    (hrow : ∀ z∈E, ‖F (parameterCode ρ (c z.1)) z.2‖ ≤ H)
    (hSS : ∀ world t, IntervalAD ζ d Kss
      {x | ∃ l, (l,t)∈E ∧ parameterCode ρ (c l)=world ∧
        zS (F world) (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t=x})
    (hRC : ∀ z∈E, ∀ z'∈E, parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
      ‖F (parameterCode ρ (c z.1)) z.2-F (parameterCode ρ (c z'.1)) z'.2‖ ≤
        Krc*(|z.2-z'.2|+ρ))
    (hResC : ∀ world, ∀ z∈E, ∀ z'∈E,
      parameterCode ρ (c z.1)=world → parameterCode ρ (c z'.1)=world →
      |zR (F world) (zoomCoefficients ρ (parameterCenter ρ world) (c z.1)) z.2-
        zR (F world) (zoomCoefficients ρ (parameterCenter ρ world) (c z'.1)) z'.2| ≤
      Kres*(‖zpos (zoomCoefficients ρ (parameterCenter ρ world) (c z.1)) z.2-
        zpos (zoomCoefficients ρ (parameterCenter ρ world) (c z'.1)) z'.2‖+ζ))
    (coarseWeight : (Fin 7 → ℤ) → ENNReal)
    (fineWeight : ℝ → (Fin 7 → ℤ) → ENNReal)
    (hcoarseFloor : ∀ z∈E,
      ENNReal.ofReal ((ρ^((2:ℝ)+d)/Kcap)*amplitude)*
        coarseWeight (parameterCode ρ (c z.1)) ≤
      ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)})
    (hfineFloor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ z∈E,
      ENNReal.ofReal (((ρ*dyadicParameterWidth (parameterLevel r))^((2:ℝ)+d)/Kcap)*amplitude)*
        fineWeight r (zoomParameterPiece ρ c r z.1) ≤
        ν {l' | zoomParameterPiece ρ c r l'=zoomParameterPiece ρ c r z.1})
    (hcoarseR : ∀ world (t a : ℝ) (b : Fin 2 → ℝ) (q : ℝ), ζ ≤ q → q ≤ 1 →
      ν {l | parameterCode ρ (c l)=world ∧ (l,t)∈R ∧
        InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
        ENNReal.ofReal (Knum*(ρ*q)^((2:ℝ)+d)*amplitude)*coarseWeight world)
    (hfineR : ∀ r, ζ ≤ r → r ≤ 1 → ∀ world fine (t a : ℝ) (b : Fin 2 → ℝ) q,
      ζ ≤ q → q ≤ r →
      ν {l | parameterCode ρ (c l)=world ∧ zoomParameterPiece ρ c r l=fine ∧ (l,t)∈R ∧
        InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
        ENNReal.ofReal (Knum*(ρ*q)^((2:ℝ)+d)*amplitude)*fineWeight r fine) :
    ∀ world, ν {l | parameterCode ρ (c l)=world} ≠ 0 →
      ∀ A : Set (Λ×ℝ), MeasurableSet A →
        A ⊆ E ∩ ({l | parameterCode ρ (c l)=world} ×ˢ univ) →
        ENNReal.ofReal H⁻¹ ≤
          (((ν {l | parameterCode ρ (c l)=world})⁻¹ •
            ν.restrict {l | parameterCode ρ (c l)=world}).prod volume) A →
        ScalarNormal
          ((ν {l | parameterCode ρ (c l)=world})⁻¹ •
            ν.restrict {l | parameterCode ρ (c l)=world})
          (fun l => zoomCoefficients ρ (parameterCenter ρ world) (c l)) A
          (F world) (zoomParameterPiece ρ c) H ζ d := by
  intro world hpositive A hA hAE hdense
  have hsub : A⊆E := hAE.trans inter_subset_left
  have hworld : ∀ l t, (l,t)∈A → parameterCode ρ (c l)=world :=
    fun l t h => (hAE h).2.1
  have hAmass : 0 <
      (((ν {l | parameterCode ρ (c l)=world})⁻¹ •
        ν.restrict {l | parameterCode ρ (c l)=world}).prod volume) A :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (zero_lt_one.trans_le hH))).trans_le hdense
  obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hAmass.ne'
  have hfloor : ENNReal.ofReal ((ρ^((2:ℝ)+d)/Kcap)*amplitude)*coarseWeight world ≤
      ν {l | parameterCode ρ (c l)=world} := by
    simpa only [hworld z.1 z.2 hz] using hcoarseFloor z (hsub hz)
  refine original_scalar_normal_world_of_prepared_incidence_caps
    ν c hc R A hA (hsub.trans hER) (F world) (hFm world)
    ρ ζ d H Kcap Knum Kss Krc Kres amplitude
    hρ hζ hζ1 hd hd1 hH hKcap hnumBudget hamp hcapH hssH hrc0 hrcH hresH hρζ
    world hworld hpositive (fun z hz => ht z (hsub hz)) ?_ hdense ?_ ?_ ?_
    (coarseWeight world) fineWeight hfloor
    (fun r hr hr1 l t hl => hfineFloor r hr hr1 (l,t) (hsub hl))
    (hcoarseR world) (fun r hr hr1 => hfineR r hr hr1 world)
  · intro z hz
    simpa only [hworld z.1 z.2 hz] using hrow z (hsub hz)
  · intro t
    apply (hSS world t).mono
    rintro x ⟨l,hl,hx⟩
    exact ⟨l,hsub hl,hworld l t hl,hx⟩
  · intro z hz z' hz'
    have hh := hRC z (hsub hz) z' (hsub hz')
      ((hworld z.1 z.2 hz).trans (hworld z'.1 z'.2 hz').symm)
    simpa only [hworld z.1 z.2 hz,hworld z'.1 z'.2 hz'] using hh
  · intro z hz z' hz'
    exact hResC world z (hsub hz) z' (hsub hz')
      (hworld z.1 z.2 hz) (hworld z'.1 z'.2 hz')

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
