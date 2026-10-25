-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CalibratedClockAtSteps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CalibratedClockAtSteps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CalibratedClockAtSteps.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CalibratedClockFloors

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ClockCalibration

open Set MeasureTheory
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal

noncomputable section

/-- Calibrated whole-cell floors at a prescribed dyadic coarsening.
The input fine mesh can therefore be chosen from an already fixed MK4
clock mesh. The exact census constant and height factor are retained. -/
theorem pointwise_floors_at_steps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hsupport : ∀ᵐ x ∂μ, x∈E)
    (z : Ω → Fin 3 → ℝ) (hz : Measurable z) (X : Ω → ℝ) (hX : Measurable X)
    {ε θ K d lossRate : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K)
    (hcensus : ∀ b w : ℝ, ε ≤ b → b ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*b ≤ θ*w → (occupied E z X b w).Finite ∧
        ((occupied E z X b w).ncard:ℝ) ≤ K/(b^3*w^d))
    (steps : ℕ) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hresolved : ε*(2:ℝ)^steps ≤ θ) (hRate : 0 ≤ lossRate) (reference : ENNReal) :
    let mesh := ε*(2:ℝ)^steps
    let code := gridCode z (fun x => θ*X x) mesh mesh
    ∃ (S : Finset ((Fin 3 → ℤ) × ℤ)) (keep : Set Ω),
      (∀ x∈E, code x∈S) ∧ MeasurableSet keep ∧
      μ keepᶜ ≤ ENNReal.ofReal ((K*((2:ℝ)^steps)^3)*lossRate)*reference ∧
      (∀ q, (μ.restrict keep) (code ⁻¹' {q})=0 ∨
        ENNReal.ofReal (lossRate*θ^(-d)*mesh^((3:ℝ)+d))*reference ≤
          (μ.restrict keep) (code ⁻¹' {q})) ∧
      (∀ x∈keep, ENNReal.ofReal (lossRate*θ^(-d)*mesh^((3:ℝ)+d))*reference ≤
        (μ.restrict keep) (code ⁻¹' {code x})) ∧
      ∀ x y, code x=code y → (x∈keep ↔ y∈keep) := by
  let mesh := ε*(2:ℝ)^steps
  have hm : 0 < mesh := by dsimp [mesh]; positivity
  have hmd : 0 < mesh^d := Real.rpow_pos_of_pos hm _
  have hθd : 0 < θ^d := Real.rpow_pos_of_pos hθ _
  obtain ⟨S,hS,hcover⟩ := clock_isotropic_support_height_calibrated E z X hε hε1 hθ hK hθK
    hcensus steps hsteps hresolved
  change (S.card:ℝ)*mesh^((3:ℝ)+d) ≤ K*θ^d*((2:ℝ)^steps)^3 at hS
  let C := K*((2:ℝ)^steps)^3
  let profile := (θ/mesh)^d
  have hprofile : 0 < profile := Real.rpow_pos_of_pos (div_pos hθ hm) _
  have hmexp : mesh^((3:ℝ)+d)=mesh^3*mesh^d := by
    rw [Real.rpow_add hm]
    norm_num
  have hcount : (S.card:ℝ)*mesh^3 ≤ C*profile := by
    dsimp only [profile]
    rw [Real.div_rpow hθ.le hm.le,←mul_div_assoc]
    apply (le_div_iff₀ hmd).mpr
    simpa only [hmexp,C,mul_assoc,mul_comm (θ^d)] using hS
  let code := gridCode z (fun x => θ*X x) mesh mesh
  have hcode : Measurable code := measurable_product_gridCode z hz _ (hX.const_mul θ) mesh mesh
  have hsupp : ∀ᵐ x ∂μ, code x∈S := hsupport.mono (fun x hx => hcover x hx)
  obtain ⟨keep,hkeep,hloss,hfloor,hpoint,hsaturated⟩ := whole_code_pruning
    μ code hcode S hsupp hm hprofile hRate reference hcount
  have hfactor : lossRate*mesh^3/profile=lossRate*θ^(-d)*mesh^((3:ℝ)+d) := by
    dsimp only [profile]
    rw [Real.div_rpow hθ.le hm.le,Real.rpow_neg hθ.le,hmexp]
    field_simp
  rw [hfactor] at hfloor hpoint
  exact ⟨S,keep,hcover,hkeep,hloss,hfloor,hpoint,hsaturated⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ClockCalibration
