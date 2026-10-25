-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ClockStateCoarsening, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ClockStateCoarsening.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ClockStateCoarsening.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockIsotropicCensus
import Submission.Lib.K4StateFractionKeep

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open MeasureTheory Set
open Submission.Lib.K4ParentSignalPreparation.Census
noncomputable section

/-- Coarsen both components of a product grid label, with independent dyadic factors. -/
def coarsenProductGrid (baseSteps heightSteps : ℕ) (q : (Fin 3 → ℤ) × ℤ) :
    (Fin 3 → ℤ) × ℤ :=
  ((fun j => q.1 j/(2:ℤ)^baseSteps),q.2/(2:ℤ)^heightSteps)

/-- The clock-scaled isotropic code is an exact function of the earlier
physical fine code whenever the height ratio is dyadic. -/
theorem clock_gridCode_dyadic_coarsening {Ω : Type*}
    (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ) {ε θ : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (baseSteps heightSteps : ℕ)
    (hscale : θ*(2:ℝ)^heightSteps=(2:ℝ)^baseSteps) (x : Ω) :
    gridCode z (fun x => θ*X x) (ε*(2:ℝ)^baseSteps) (ε*(2:ℝ)^baseSteps) x =
      coarsenProductGrid baseSteps heightSteps (gridCode z X ε ε x) := by
  have hwidth : (ε*(2:ℝ)^baseSteps)/θ=ε*(2:ℝ)^heightSteps := by
    rw [←hscale]
    field_simp
  rw [gridCode_scale z X hθ (by positivity),hwidth]
  unfold gridCode coarsenProductGrid
  congr 1
  · funext j
    rw [div_mul_eq_div_div,Submission.Lib.K4XInterface.floor_div_two_pow]
  · rw [div_mul_eq_div_div,Submission.Lib.K4XInterface.floor_div_two_pow]

/-- A dyadic height conversion bounded by the output base coarsening
has an integer dyadic coarsening on its height component. -/
theorem exists_dyadic_height_coarsening {θ : ℝ} (exponent : ℤ) (hθ : θ=(2:ℝ)^exponent)
    (baseSteps : ℕ) (hbound : θ ≤ (2:ℝ)^baseSteps) :
    ∃ heightSteps : ℕ, θ*(2:ℝ)^heightSteps=(2:ℝ)^baseSteps := by
  have he : exponent ≤ (baseSteps:ℤ) := by
    apply (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp
    simpa only [hθ,zpow_natCast] using hbound
  let heightSteps := ((baseSteps:ℤ)-exponent).toNat
  have hcast : (heightSteps:ℤ)=(baseSteps:ℤ)-exponent := Int.toNat_of_nonneg (by omega)
  refine ⟨heightSteps,?_⟩
  rw [hθ,←zpow_natCast,hcast,←zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  simp

/-- Conditional ratios pass to every deterministic coarsening of a
countable measurable state, with the same ratio. The original law stays fixed. -/
theorem state_ratio_under_map {Ω I J : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) (state : Ω → I) (hstate : Measurable state)
    (mapState : I → J) (S : Set Ω) (hS : MeasurableSet S) (η : ENNReal)
    (hη : ∀ i, μ (state ⁻¹' {i}∩S) ≤ η*μ (state ⁻¹' {i})) (j : J) :
    μ {x | mapState (state x)=j ∧ x∈S} ≤ η*μ {x | mapState (state x)=j} := by
  have hwhole : Submission.Lib.K4StateFractionKeep.fractionKeep μ state univ 1=univ := by
    ext x
    simp [Submission.Lib.K4StateFractionKeep.fractionKeep,Submission.Lib.K4StateFractionKeep.goodStates]
  have hh := Submission.Lib.K4StateFractionKeep.fractionKeep_union_ratio μ hstate MeasurableSet.univ
    (f:=1) (by norm_num) (by norm_num) hS η hη {i | mapState i=j}
  have hset : state ⁻¹' {i | mapState i=j}∩S={x | mapState (state x)=j ∧ x∈S} := by
    ext x
    simp
  have hset' : state ⁻¹' {i | mapState i=j}={x | mapState (state x)=j} := by
    ext x
    simp
  simp only [hwhole,univ_inter,div_one] at hh
  rw [hset,hset'] at hh
  exact hh

/-- Cutting a union of whole cells preserves every conditional ratio on
those same cells. This does not assert preservation under arbitrary cuts. -/
theorem state_ratio_under_whole_cell_cut {Ω I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : Measure Ω) (state : Ω → I) (hstate : Measurable state) (keep : Set Ω)
    (hsaturated : ∀ x y, state x=state y → (x∈keep ↔ y∈keep))
    (S : Set Ω) (η : ENNReal)
    (hη : ∀ i, μ (state ⁻¹' {i}∩S) ≤ η*μ (state ⁻¹' {i})) (i : I) :
    (μ.restrict keep) (state ⁻¹' {i}∩S) ≤ η*(μ.restrict keep) (state ⁻¹' {i}) := by
  by_cases hi : ∃ x∈keep, state x=i
  · obtain ⟨x,hx,hxi⟩ := hi
    have hsub : state ⁻¹' {i}⊆keep := by
      intro y hy
      exact (hsaturated y x (hy.trans hxi.symm)).mpr hx
    have hmass : (μ.restrict keep) (state ⁻¹' {i})=μ (state ⁻¹' {i}) := by
      rw [Measure.restrict_apply (hstate (measurableSet_singleton i)),inter_eq_left.mpr hsub]
    calc
      _ ≤ μ (state ⁻¹' {i}∩S) := Measure.restrict_le_self _
      _ ≤ η*μ (state ⁻¹' {i}) := hη i
      _ = _ := by rw [hmass]
  · have hempty : state ⁻¹' {i}∩keep=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hi ⟨x,hx.2,hx.1⟩
    have hmass : (μ.restrict keep) (state ⁻¹' {i})=0 := by
      rw [Measure.restrict_apply (hstate (measurableSet_singleton i)),hempty,measure_empty]
    calc
      _ ≤ (μ.restrict keep) (state ⁻¹' {i}) := measure_mono inter_subset_left
      _ = 0 := hmass
      _ ≤ _ := zero_le

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
