-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.DyadicOriginalWorldFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.IncidenceWorldControl
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalDyadicParameterFloors

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- The coefficient cleanup's finite dyadic floors supply the coarse
world floor and EVERY real-query fine world floor. Their velocity
palettes are the exact pushforwards of one unchanged original reference. -/
theorem original_world_floors_of_dyadic_floors {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (π : Measure (Fin 2 → ℝ))
    {ρ ζ dimension ε Kcap amplitude : ℝ} (hρ : 0 < ρ) (hζ : 0 < ζ)
    (hε : 0 ≤ ε) (hKcap : 0 < Kcap)
    (n L : ℕ) (hρdyadic : ρ=dyadicParameterWidth n)
    (hL : parameterLevel ζ+1 ≤ L)
    (hbudget : amplitude/Kcap ≤ (dyadicParameterWidth (n+L-1))^ε)
    (hfloor : ∀ i : Fin L, ∀ z∈E,
      ENNReal.ofReal ((dyadicParameterWidth (n+i.val))^((2:ℝ)+dimension)*
        (dyadicParameterWidth (n+i.val))^ε)*
        (π.map (parameterCode (dyadicParameterWidth (n+i.val))))
          {vbin (dyadicParameterWidth (n+i.val)) (c z.1)} ≤
        ν {l | parameterCode (dyadicParameterWidth (n+i.val)) (c l)=
          parameterCode (dyadicParameterWidth (n+i.val)) (c z.1)}) :
    (∀ z∈E, ENNReal.ofReal ((ρ^((2:ℝ)+dimension)/Kcap)*amplitude)*
      π {v | parameterCode ρ v=parameterVelocityHeader (parameterCode ρ (c z.1))} ≤
        ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)}) ∧
    (∀ r, ζ ≤ r → r ≤ 1 → ∀ z∈E,
      ENNReal.ofReal (((ρ*dyadicParameterWidth (parameterLevel r))^((2:ℝ)+dimension)/Kcap)*amplitude)*
        π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=
          parameterVelocityHeader (zoomParameterPiece ρ c r z.1)} ≤
        ν {l | zoomParameterPiece ρ c r l=zoomParameterPiece ρ c r z.1}) := by
  have hvelocity (w : ℝ) (cf : Fin 7 → ℝ) : vbin w cf=parameterCode w (zv cf) := rfl
  have hcoarse (i : Fin L) (z : Λ × ℝ) (hz : z∈E) :
      ENNReal.ofReal (((dyadicParameterWidth (n+i.val))^((2:ℝ)+dimension)/Kcap)*amplitude)*
        π {v | parameterCode (dyadicParameterWidth (n+i.val)) v=
          parameterVelocityHeader (parameterCode (dyadicParameterWidth (n+i.val)) (c z.1))} ≤
        ν {l | parameterCode (dyadicParameterWidth (n+i.val)) (c l)=
          parameterCode (dyadicParameterWidth (n+i.val)) (c z.1)} := by
    have hwidth : dyadicParameterWidth (n+L-1) ≤ dyadicParameterWidth (n+i.val) :=
      dyadicParameterWidth_antitone (by omega)
    have hpower : amplitude/Kcap ≤ (dyadicParameterWidth (n+i.val))^ε :=
      hbudget.trans (Real.rpow_le_rpow (dyadicParameterWidth_pos _).le hwidth hε)
    have hnum : ((dyadicParameterWidth (n+i.val))^((2:ℝ)+dimension)/Kcap)*amplitude ≤
        (dyadicParameterWidth (n+i.val))^((2:ℝ)+dimension)*
          (dyadicParameterWidth (n+i.val))^ε := by
      calc
        _ = (dyadicParameterWidth (n+i.val))^((2:ℝ)+dimension)*(amplitude/Kcap) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg (dyadicParameterWidth_pos _).le _)
    apply le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hnum) le_rfl)
    have h := hfloor i z hz
    rw [Measure.map_apply (measurable_parameterCode _) (measurableSet_singleton _)] at h
    simpa only [parameterVelocityHeader_code,hvelocity,Set.preimage,mem_singleton_iff] using h
  have hscale (j : ℕ) : ρ*dyadicParameterWidth j=dyadicParameterWidth (n+j) := by
    rw [hρdyadic]
    simp only [dyadicParameterWidth,pow_add,mul_inv_rev]
    ring
  constructor
  · intro z hz
    let i : Fin L := ⟨0,by omega⟩
    simpa only [i,Nat.add_zero,←hρdyadic] using hcoarse i z hz
  · intro r hr hr1 z hz
    have hi : parameterLevel r < L :=
      (parameterLevel_below_floor hζ hr hr1).trans_le hL
    let i : Fin L := ⟨parameterLevel r,hi⟩
    simpa only [i,zoomParameterPiece,hscale] using hcoarse i z hz

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
