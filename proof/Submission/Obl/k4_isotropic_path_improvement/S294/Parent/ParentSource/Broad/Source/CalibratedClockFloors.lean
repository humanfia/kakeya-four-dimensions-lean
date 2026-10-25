-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CalibratedClockFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CalibratedClockFloors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CalibratedClockFloors.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CalibratedClockCensus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.WholeCodePruning

/-!
# Clock cell floors with the exact height factor

The measurable code and whole-cell organization adapt o265/x0943, commit
4fa13b3cf, Broad/Source/ClockIsotropicFloors.lean. The calibrated support and
floor profile preserve the height factor rather than replacing it by an envelope.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ClockCalibration
open MeasureTheory Set
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal
noncomputable section

theorem measurable_product_gridCode {Ω : Type*} [MeasurableSpace Ω]
    (z : Ω → Fin 3 → ℝ) (hz : Measurable z) (X : Ω → ℝ) (hX : Measurable X)
    (base hidden : ℝ) : Measurable (gridCode z X base hidden) := by
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro i
    exact Int.measurable_floor.comp (((measurable_pi_apply i).comp hz).div_const base)
  · exact Int.measurable_floor.comp (hX.div_const hidden)

/-- Whole isotropic cells for the clock-scaled signal have the calibrated
pointwise mass floor, measured against the original reference. -/
theorem pointwise_floors {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hsupport : ∀ᵐ x ∂μ, x∈E)
    (z : Ω → Fin 3 → ℝ) (hz : Measurable z) (X : Ω → ℝ) (hX : Measurable X)
    {ε θ K d ζ lossRate : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K)
    (hεζ : ε ≤ θ*ζ) (hεζplain : ε ≤ ζ) (hmargin : 2*K^(100:ℕ)*ζ ≤ 1)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ θ*w → (occupied E z X p w).Finite ∧
        ((occupied E z X p w).ncard : ℝ) ≤ K/(p^3*w^d))
    (hRate : 0 ≤ lossRate) (reference : ENNReal) :
    ∃ (steps : ℕ) (keep : Set Ω), K^(100:ℕ) ≤ (2:ℝ)^steps ∧
      (2:ℝ)^steps ≤ 2*K^(100:ℕ) ∧
      let mesh := ε*(2:ℝ)^steps
      MeasurableSet keep ∧ ε ≤ mesh ∧ mesh ≤ 1 ∧ mesh ≤ θ ∧
      μ keepᶜ ≤ ENNReal.ofReal (8*K^(301:ℕ)*lossRate)*reference ∧
      (∀ x∈keep, ENNReal.ofReal (lossRate*θ^(-d)*mesh^((3:ℝ)+d))*reference ≤
        (μ.restrict keep) {y | gridCode z (fun y => θ*X y) mesh mesh y=
          gridCode z (fun y => θ*X y) mesh mesh x}) ∧
      ∀ x y, gridCode z (fun y => θ*X y) mesh mesh x=
          gridCode z (fun y => θ*X y) mesh mesh y → (x∈keep ↔ y∈keep) := by
  obtain ⟨steps,S,hlo,hhi,heps,hres,hcount,hcover⟩ :=
    clock_isotropic_support_height_calibrated_precision E z X hε hε1 hθ hK hθK
      hεζ hmargin hcensus
  let mesh := ε*(2:ℝ)^steps
  have hm : 0 < mesh := by dsimp [mesh]; positivity
  have hmd : 0 < mesh^d := Real.rpow_pos_of_pos hm d
  have hθd : 0 < θ^d := Real.rpow_pos_of_pos hθ d
  have hprofile : 0 < (θ/mesh)^d := Real.rpow_pos_of_pos (div_pos hθ hm) d
  have hmexp : mesh^((3:ℝ)+d)=mesh^3*mesh^d := by rw [Real.rpow_add hm]; norm_num
  change (S.card : ℝ)*mesh^((3:ℝ)+d) ≤ 8*K^(301:ℕ)*θ^d at hcount
  have hbaseCount : (S.card : ℝ)*mesh^3 ≤ (8*K^(301:ℕ))*(θ/mesh)^d := by
    rw [Real.div_rpow hθ.le hm.le,←mul_div_assoc]
    apply (le_div_iff₀ hmd).mpr
    simpa only [hmexp,mul_assoc] using hcount
  let code := gridCode z (fun x => θ*X x) mesh mesh
  have hcode : Measurable code := measurable_product_gridCode z hz _ (hX.const_mul θ) _ _
  have hsupp : ∀ᵐ x ∂μ, code x∈S := hsupport.mono (fun x hx => hcover x hx)
  obtain ⟨keep,hkeep,hloss,-,hpoint,hsaturated⟩ := whole_code_pruning
    μ code hcode S hsupp hm hprofile hRate reference hbaseCount
  have hm1 : mesh ≤ 1 := by
    have hζ : 0 ≤ ζ := hε.le.trans hεζplain
    calc
      _ ≤ ζ*(2:ℝ)^steps := mul_le_mul_of_nonneg_right hεζplain (by positivity)
      _ ≤ ζ*(2*K^(100:ℕ)) := mul_le_mul_of_nonneg_left hhi hζ
      _ = 2*K^(100:ℕ)*ζ := by ring
      _ ≤ 1 := hmargin
  have hfloor : lossRate*mesh^3/(θ/mesh)^d=lossRate*θ^(-d)*mesh^((3:ℝ)+d) := by
    rw [Real.div_rpow hθ.le hm.le,Real.rpow_neg hθ.le,hmexp]
    field_simp
  refine ⟨steps,keep,hlo,hhi,hkeep,heps,hm1,hres,hloss,?_,hsaturated⟩
  intro x hx
  have hh := hpoint x hx
  rw [hfloor] at hh
  exact hh

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ClockCalibration
