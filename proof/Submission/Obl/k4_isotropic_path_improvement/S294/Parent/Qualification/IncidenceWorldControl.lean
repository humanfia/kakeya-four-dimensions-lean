-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.IncidenceWorldControl, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PreparedWorldBuilder
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CurrentVelocitySpatialCaps

/-! Original world estimates after current-incidence preparation.

The estimates are imposed on one source, never on each possible failure
restriction. Their support, row and residual clauses pass to all later
restrictions, while the coefficient-bin floors keep the full original
prior and the same external velocity reference.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped ENNReal

noncomputable section

/-- The subset-stable estimates needed in addition to the spatial caps.
There is no density premise on every world. -/
structure OriginalWorldControl {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ)
    (ρ ζ d H Kcap Kss Krc Kres amplitude : ℝ)
    (π : Measure (Fin 2 → ℝ)) : Prop where
  measurable_row : ∀ world, Measurable (F world)
  row : ∀ z∈E, ‖F (parameterCode ρ (c z.1)) z.2‖ ≤ H
  support : ∀ world t, IntervalAD ζ d Kss
    {x | ∃ l, (l,t)∈E ∧ parameterCode ρ (c l)=world ∧
      zS (F world) (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t=x}
  row_comparison : ∀ z∈E, ∀ z'∈E,
    parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
    ‖F (parameterCode ρ (c z.1)) z.2-F (parameterCode ρ (c z'.1)) z'.2‖ ≤
      Krc*(|z.2-z'.2|+ρ)
  residual_comparison : ∀ world, ∀ z∈E, ∀ z'∈E,
    parameterCode ρ (c z.1)=world → parameterCode ρ (c z'.1)=world →
    |zR (F world) (zoomCoefficients ρ (parameterCenter ρ world) (c z.1)) z.2-
      zR (F world) (zoomCoefficients ρ (parameterCenter ρ world) (c z'.1)) z'.2| ≤
      Kres*(‖zpos (zoomCoefficients ρ (parameterCenter ρ world) (c z.1)) z.2-
        zpos (zoomCoefficients ρ (parameterCenter ρ world) (c z'.1)) z'.2‖+ζ)
  coarse_floor : ∀ z∈E,
    ENNReal.ofReal ((ρ^((2:ℝ)+d)/Kcap)*amplitude)*
      π {v | parameterCode ρ v=parameterVelocityHeader (parameterCode ρ (c z.1))} ≤
    ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)}
  fine_floor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ z∈E,
    ENNReal.ofReal (((ρ*dyadicParameterWidth (parameterLevel r))^((2:ℝ)+d)/Kcap)*amplitude)*
      π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=
        parameterVelocityHeader (zoomParameterPiece ρ c r z.1)} ≤
    ν {l | zoomParameterPiece ρ c r l=zoomParameterPiece ρ c r z.1}

/-- All additional world estimates survive arbitrary subsequent cuts. -/
theorem OriginalWorldControl.mono {Λ : Type*} [MeasurableSpace Λ]
    {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E S : Set (Λ × ℝ)}
    {F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ}
    {ρ ζ d H Kcap Kss Krc Kres amplitude : ℝ} {π : Measure (Fin 2 → ℝ)}
    (h : OriginalWorldControl ν c E F ρ ζ d H Kcap Kss Krc Kres amplitude π)
    (hSE : S⊆E) :
    OriginalWorldControl ν c S F ρ ζ d H Kcap Kss Krc Kres amplitude π where
  measurable_row := h.measurable_row
  row := fun z hz => h.row z (hSE hz)
  support := fun world t => (h.support world t).mono (by
    rintro x ⟨l,hl,hw,hx⟩
    exact ⟨l,hSE hl,hw,hx⟩)
  row_comparison := fun z hz z' hz' => h.row_comparison z (hSE hz) z' (hSE hz')
  residual_comparison := fun world z hz z' hz' =>
    h.residual_comparison world z (hSE hz) z' (hSE hz')
  coarse_floor := fun z hz => h.coarse_floor z (hSE hz)
  fine_floor := fun r hr hr1 z hz => h.fine_floor r hr hr1 z (hSE hz)

/-- The actual original-prior builder, with the discrete velocity
reference weights read directly from the prepared spatial cap source. -/
theorem OriginalWorldControl.scalar_normal_builder {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (R E : Set (Λ × ℝ)) (hER : E⊆R)
    (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ)
    (ρ ζ d H Kcap Knum Kss Krc Kres amplitude : ℝ)
    (hρ : 0 < ρ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : 0 ≤ d) (hd1 : d < 1)
    (hH : 1 ≤ H) (hKcap : 0 < Kcap) (hnum : Knum ≤ Kcap) (hamp : 0 ≤ amplitude)
    (hcapH : 8*Kcap^2 ≤ H) (hssH : Kss ≤ H) (hrc0 : 0 ≤ Krc) (hrcH : Krc ≤ H)
    (hresH : Kres ≤ H) (hρζ : ρ ≤ ζ)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1) (π : Measure (Fin 2 → ℝ))
    (control : OriginalWorldControl ν c E F ρ ζ d H Kcap Kss Krc Kres amplitude π)
    (hcoarse : ∀ world (t a : ℝ) (b : Fin 2 → ℝ) q, ζ ≤ q → q ≤ 1 →
      ν {l | parameterCode ρ (c l)=world ∧ (l,t)∈R ∧
        InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
      ENNReal.ofReal (Knum*(ρ*q)^((2:ℝ)+d)*amplitude)*
        π {v | parameterCode ρ v=parameterVelocityHeader world})
    (hfine : ∀ r, ζ ≤ r → r ≤ 1 → ∀ world fine (t a : ℝ) (b : Fin 2 → ℝ) q,
      ζ ≤ q → q ≤ r →
      ν {l | parameterCode ρ (c l)=world ∧ zoomParameterPiece ρ c r l=fine ∧ (l,t)∈R ∧
        InCube (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t a b q} ≤
      ENNReal.ofReal (Knum*(ρ*q)^((2:ℝ)+d)*amplitude)*
        π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=
          parameterVelocityHeader fine}) :
    ∀ world, ν {l | parameterCode ρ (c l)=world} ≠ 0 →
      ∀ A : Set (Λ × ℝ), MeasurableSet A →
        A⊆E∩({l | parameterCode ρ (c l)=world} ×ˢ univ) →
        ENNReal.ofReal H⁻¹ ≤
          (((ν {l | parameterCode ρ (c l)=world})⁻¹ •
            ν.restrict {l | parameterCode ρ (c l)=world}).prod volume) A →
        ScalarNormal
          ((ν {l | parameterCode ρ (c l)=world})⁻¹ •
            ν.restrict {l | parameterCode ρ (c l)=world})
          (fun l => zoomCoefficients ρ (parameterCenter ρ world) (c l)) A
          (F world) (zoomParameterPiece ρ c) H ζ d := by
  exact original_scalar_normal_builder_of_prepared_incidence_caps ν c hc R E hER F
    control.measurable_row ρ ζ d H Kcap Knum Kss Krc Kres amplitude
    hρ hζ hζ1 hd hd1 hH hKcap hnum hamp hcapH hssH hrc0 hrcH hresH hρζ ht
    control.row control.support control.row_comparison control.residual_comparison
    (fun world => π {v | parameterCode ρ v=parameterVelocityHeader world})
    (fun r fine => π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=
      parameterVelocityHeader fine})
    control.coarse_floor control.fine_floor hcoarse hfine

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
