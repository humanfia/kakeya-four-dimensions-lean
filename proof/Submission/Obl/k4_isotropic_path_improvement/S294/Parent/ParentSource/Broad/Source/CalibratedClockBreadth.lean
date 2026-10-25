-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CalibratedClockBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CalibratedClockBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit c1f30c34,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CalibratedClockBreadth.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CalibratedClockFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockStateCoarsening

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ClockCalibration

open MeasureTheory Set
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal

noncomputable section

/-- Calibrated clock-cell floors and every original fine-state ratio hold
under the same retained law. The cut keeps whole coarse cells. -/
theorem floors_with_state_ratios {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hsupport : ∀ᵐ x ∂μ, x∈E)
    (z : Ω → Fin 3 → ℝ) (hz : Measurable z) (X : Ω → ℝ) (hX : Measurable X)
    {ε θ K d ζ lossRate : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K)
    (hεζ : ε ≤ θ*ζ) (hεζplain : ε ≤ ζ) (hmargin : 2*K^(100:ℕ)*ζ ≤ 1)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ θ*w → (occupied E z X p w).Finite ∧
        ((occupied E z X p w).ncard : ℝ) ≤ K/(p^3*w^d))
    (exponent : ℤ) (hdyadic : θ=(2:ℝ)^exponent)
    (hRate : 0 ≤ lossRate) (reference : ENNReal) :
    ∃ (steps : ℕ) (keep : Set Ω), K^(100:ℕ) ≤ (2:ℝ)^steps ∧
      (2:ℝ)^steps ≤ 2*K^(100:ℕ) ∧
      let mesh := ε*(2:ℝ)^steps
      MeasurableSet keep ∧ ε ≤ mesh ∧ mesh ≤ 1 ∧ mesh ≤ θ ∧
      μ keepᶜ ≤ ENNReal.ofReal (8*K^(301:ℕ)*lossRate)*reference ∧
      (∀ x∈keep, ENNReal.ofReal (lossRate*θ^(-d)*mesh^((3:ℝ)+d))*reference ≤
        (μ.restrict keep) {y | gridCode z (fun y => θ*X y) mesh mesh y=
          gridCode z (fun y => θ*X y) mesh mesh x}) ∧
      (∀ x y, gridCode z (fun y => θ*X y) mesh mesh x=
        gridCode z (fun y => θ*X y) mesh mesh y → (x∈keep ↔ y∈keep)) ∧
      ∀ (band : Set Ω), MeasurableSet band → ∀ η : ENNReal,
        (∀ i, μ ((gridCode z X ε ε) ⁻¹' {i}∩band) ≤ η*μ ((gridCode z X ε ε) ⁻¹' {i})) →
        ∀ i, (μ.restrict keep) ((gridCode z (fun y => θ*X y) mesh mesh) ⁻¹' {i}∩band) ≤
          η*(μ.restrict keep) ((gridCode z (fun y => θ*X y) mesh mesh) ⁻¹' {i}) := by
  obtain ⟨steps,keep,hlo,hhi,hkeep,heps,hm1,hres,hloss,hpoint,hsaturated⟩ :=
    pointwise_floors μ E hsupport z hz X hX hε hε1 hθ hK hθK
      hεζ hεζplain hmargin hcensus hRate reference
  let mesh := ε*(2:ℝ)^steps
  let fine := gridCode z X ε ε
  let coarse := gridCode z (fun x => θ*X x) mesh mesh
  have hKpow : K ≤ K^(100:ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by norm_num : (1:ℕ) ≤ 100)
  obtain ⟨heightSteps,hscale⟩ := exists_dyadic_height_coarsening exponent hdyadic steps
    (hθK.trans (hKpow.trans hlo))
  let mapState := coarsenProductGrid steps heightSteps
  have hfactor (x : Ω) : coarse x=mapState (fine x) :=
    clock_gridCode_dyadic_coarsening z X hε hθ steps heightSteps hscale x
  have hfine : Measurable fine := measurable_product_gridCode z hz X hX ε ε
  have hcoarse : Measurable coarse := measurable_product_gridCode z hz _ (hX.const_mul θ) mesh mesh
  refine ⟨steps,keep,hlo,hhi,hkeep,heps,hm1,hres,hloss,hpoint,hsaturated,?_⟩
  intro band hband η hη i
  have hbefore (j : (Fin 3 → ℤ) × ℤ) : μ (coarse ⁻¹' {j}∩band) ≤ η*μ (coarse ⁻¹' {j}) := by
    have hh := state_ratio_under_map μ fine hfine mapState band hband η hη j
    have hset : coarse ⁻¹' {j}∩band={x | mapState (fine x)=j ∧ x∈band} := by
      ext x
      simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq,hfactor]
    have hset' : coarse ⁻¹' {j}={x | mapState (fine x)=j} := by
      ext x
      simp only [mem_preimage,mem_singleton_iff,mem_ofPred_eq,hfactor]
    rw [hset,hset']
    exact hh
  exact state_ratio_under_whole_cell_cut μ coarse hcoarse keep hsaturated band η hbefore i

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ClockCalibration
