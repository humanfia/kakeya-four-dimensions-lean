-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalDyadicFloorData, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicOriginalWorldFloors

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Full ORIGINAL coefficient-bin floors on one finite consecutive
dyadic grid. The palette is one fixed original velocity probability;
its displayed bin laws are literal pushforwards of that probability. -/
structure OriginalDyadicFloorData {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (palette : Measure (Fin 2 → ℝ)) (dimension exponent : ℝ) (start count : ℕ) : Prop where
  probability : IsProbabilityMeasure palette
  floor : ∀ i : Fin count, ∀ z∈E,
    ENNReal.ofReal ((dyadicParameterWidth (start+i.val))^((2:ℝ)+dimension)*
      (dyadicParameterWidth (start+i.val))^exponent)*
      (palette.map (parameterCode (dyadicParameterWidth (start+i.val))))
        {vbin (dyadicParameterWidth (start+i.val)) (c z.1)} ≤
      ν {l | parameterCode (dyadicParameterWidth (start+i.val)) (c l)=
        parameterCode (dyadicParameterWidth (start+i.val)) (c z.1)}

section Data

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {palette : Measure (Fin 2 → ℝ)}
    {dimension exponent : ℝ} {start count : ℕ}
    (data : OriginalDyadicFloorData ν c E palette dimension exponent start count)

include data

/-- Later source restrictions leave every original prior atom and
velocity palette unchanged. -/
theorem OriginalDyadicFloorData.restrict {S : Set (Λ × ℝ)} (hSE : S⊆E) :
    OriginalDyadicFloorData ν c S palette dimension exponent start count :=
  ⟨data.probability,fun i z hz => data.floor i z (hSE hz)⟩

/-- A single floor in original velocity-reference form, ready for both
the residual snapshots and the native coarse/fine world interfaces. -/
theorem OriginalDyadicFloorData.at_width {Kcap amplitude : ℝ}
    (hexponent : 0 ≤ exponent) (hreserve : amplitude/Kcap ≤
      (dyadicParameterWidth (start+count-1))^exponent)
    (i : Fin count) (z : Λ × ℝ) (hz : z∈E) :
    ENNReal.ofReal (((dyadicParameterWidth (start+i.val))^((2:ℝ)+dimension)/Kcap)*amplitude)*
      palette {v | parameterCode (dyadicParameterWidth (start+i.val)) v=
        parameterVelocityHeader (parameterCode (dyadicParameterWidth (start+i.val)) (c z.1))} ≤
      ν {l | parameterCode (dyadicParameterWidth (start+i.val)) (c l)=
        parameterCode (dyadicParameterWidth (start+i.val)) (c z.1)} := by
  have hw : dyadicParameterWidth (start+count-1) ≤ dyadicParameterWidth (start+i.val) :=
    dyadicParameterWidth_antitone (by omega)
  have hp : amplitude/Kcap ≤ (dyadicParameterWidth (start+i.val))^exponent :=
    hreserve.trans (Real.rpow_le_rpow (dyadicParameterWidth_pos _).le hw hexponent)
  have hnum : ((dyadicParameterWidth (start+i.val))^((2:ℝ)+dimension)/Kcap)*amplitude ≤
      (dyadicParameterWidth (start+i.val))^((2:ℝ)+dimension)*
        (dyadicParameterWidth (start+i.val))^exponent := by
    calc
      _ = (dyadicParameterWidth (start+i.val))^((2:ℝ)+dimension)*(amplitude/Kcap) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (dyadicParameterWidth_pos _).le _)
  apply (mul_le_mul' (ENNReal.ofReal_le_ofReal hnum) le_rfl).trans
  have hh := data.floor i z hz
  rw [Measure.map_apply (measurable_parameterCode _) (measurableSet_singleton _)] at hh
  have hvelocity (w : ℝ) (cf : Fin 7 → ℝ) :
      vbin w cf=parameterCode w (zv cf) := rfl
  simpa only [hvelocity,parameterVelocityHeader_code,Set.preimage,mem_singleton_iff] using hh

/-- Query any level of the prepared grid without changing the
original prior, reference palette or endpoint reserve. -/
theorem OriginalDyadicFloorData.at_level {Kcap amplitude : ℝ}
    (hexponent : 0 ≤ exponent) (hreserve : amplitude/Kcap ≤
      (dyadicParameterWidth (start+count-1))^exponent)
    (level : ℕ) (hstart : start ≤ level) (hstop : level < start+count)
    (z : Λ × ℝ) (hz : z∈E) :
    ENNReal.ofReal (((dyadicParameterWidth level)^((2:ℝ)+dimension)/Kcap)*amplitude)*
      palette {v | parameterCode (dyadicParameterWidth level) v=
        parameterVelocityHeader (parameterCode (dyadicParameterWidth level) (c z.1))} ≤
      ν {l | parameterCode (dyadicParameterWidth level) (c l)=
        parameterCode (dyadicParameterWidth level) (c z.1)} := by
  let i : Fin count := ⟨level-start,by omega⟩
  have hi : start+i.val=level := by dsimp only [i]; omega
  simpa only [hi] using data.at_width hexponent hreserve i z hz

/-- The same original floor in discrete velocity-bin form. -/
theorem OriginalDyadicFloorData.at_level_bin {Kcap amplitude : ℝ}
    (hexponent : 0 ≤ exponent) (hreserve : amplitude/Kcap ≤
      (dyadicParameterWidth (start+count-1))^exponent)
    (level : ℕ) (hstart : start ≤ level) (hstop : level < start+count)
    (z : Λ × ℝ) (hz : z∈E) :
    ENNReal.ofReal (((dyadicParameterWidth level)^((2:ℝ)+dimension)/Kcap)*amplitude)*
      (palette.map (parameterCode (dyadicParameterWidth level)))
        {vbin (dyadicParameterWidth level) (c z.1)} ≤
      ν {l | parameterCode (dyadicParameterWidth level) (c l)=
        parameterCode (dyadicParameterWidth level) (c z.1)} := by
  rw [Measure.map_apply (measurable_parameterCode _) (measurableSet_singleton _)]
  have hvelocity (w : ℝ) (cf : Fin 7 → ℝ) : vbin w cf=parameterCode w (zv cf) := rfl
  simpa only [hvelocity,parameterVelocityHeader_code,Set.preimage,mem_singleton_iff] using
    data.at_level hexponent hreserve level hstart hstop z hz

/-- One pre-state floor record gives all native real-query floors.
The finite grid can extend farther for sparse residual snapshots. -/
theorem OriginalDyadicFloorData.world_floors {ρ ζ Kcap amplitude : ℝ}
    (hρ : 0 < ρ) (hζ : 0 < ζ) (hexponent : 0 ≤ exponent) (hKcap : 0 < Kcap)
    (hρdyadic : ρ=dyadicParameterWidth start) (hcount : parameterLevel ζ+1 ≤ count)
    (hreserve : amplitude/Kcap ≤ (dyadicParameterWidth (start+count-1))^exponent) :
    (∀ z∈E, ENNReal.ofReal ((ρ^((2:ℝ)+dimension)/Kcap)*amplitude)*
      palette {v | parameterCode ρ v=parameterVelocityHeader (parameterCode ρ (c z.1))} ≤
        ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)}) ∧
    (∀ r, ζ ≤ r → r ≤ 1 → ∀ z∈E,
      ENNReal.ofReal (((ρ*dyadicParameterWidth (parameterLevel r))^((2:ℝ)+dimension)/Kcap)*amplitude)*
        palette {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=
          parameterVelocityHeader (zoomParameterPiece ρ c r z.1)} ≤
        ν {l | zoomParameterPiece ρ c r l=zoomParameterPiece ρ c r z.1}) :=
  original_world_floors_of_dyadic_floors ν c E palette hρ hζ hexponent hKcap start count
    hρdyadic hcount hreserve data.floor

end Data

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
