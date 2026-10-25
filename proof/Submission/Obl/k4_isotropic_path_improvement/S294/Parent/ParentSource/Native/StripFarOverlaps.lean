-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripFarOverlaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripFarOverlaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripFarOverlaps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripFarOverlaps.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripFarOverlaps.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripParameterBins

/-! Far intersections of the enlarged heavy representatives can be discarded
once under the fixed coarse palette. Their number may be a fixed small power;
the observation lists will depend on the coarser parameter bins instead. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace BigOperators

def stripFarOverlap {ι : Type*} (n : ι → StripSpace) (β : ι → ℝ)
    (w ρ T : ℝ) : Set StripSpace := by
  classical
  exact ⋃ i, ⋃ j, if ρ ≤ ‖n i - n j‖ + |β i - β j| ∧
      ρ ≤ ‖n i + n j‖ + |β i + β j| then
    boundedStrip (n i) (β i) w T ∩ boundedStrip (n j) (β j) w T else ∅

theorem measurableSet_stripFarOverlap {ι : Type*} [Countable ι]
    (n : ι → StripSpace) (β : ι → ℝ) (w ρ T : ℝ) :
    MeasurableSet (stripFarOverlap n β w ρ T) := by
  classical
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  split_ifs
  · exact (measurableSet_boundedStrip _ _ _ _).inter
      (measurableSet_boundedStrip _ _ _ _)
  · exact MeasurableSet.empty

/-- The only heavy-family count in this estimate is the polynomial number
of pairs. It need not fit into the final requested observation slack. -/
theorem stripFarOverlap_mass_le {ι : Type*} [Fintype ι]
    (μ : Measure StripSpace) (n : ι → StripSpace) (β : ι → ℝ)
    {w ρ T ε : ℝ} (hn : ∀ i, ‖n i‖ = 1) (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hsmall : 4 * w ≤ ρ)
    (hcap : ∀ x : StripSpace,
      μ (Metric.closedBall x (32 * (1 + T) * w / ρ)) ≤ ENNReal.ofReal ε) :
    μ (stripFarOverlap n β w ρ T) ≤
      (Fintype.card ι : ENNReal) ^ 2 * ENNReal.ofReal ε := by
  classical
  have hpair (i j : ι) :
      μ (if ρ ≤ ‖n i - n j‖ + |β i - β j| ∧
          ρ ≤ ‖n i + n j‖ + |β i + β j| then
        boundedStrip (n i) (β i) w T ∩ boundedStrip (n j) (β j) w T else ∅) ≤
        ENNReal.ofReal ε := by
    split_ifs with h
    · exact bounded_strip_intersection_mass_le μ (hn i) (hn j) hT hρ hsmall
        h.1 h.2 hcap
    · simp
  calc
    _ ≤ ∑' i : ι, μ (⋃ j : ι, if ρ ≤ ‖n i - n j‖ + |β i - β j| ∧
          ρ ≤ ‖n i + n j‖ + |β i + β j| then
        boundedStrip (n i) (β i) w T ∩ boundedStrip (n j) (β j) w T else ∅) :=
      measure_iUnion_le _
    _ ≤ ∑' i : ι, ∑' j : ι, ENNReal.ofReal ε := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (hpair i))
    _ = _ := by simp [tsum_fintype, pow_two, mul_assoc]

theorem stripFarOverlap_real_mass_le {ι : Type*} [Fintype ι]
    (μ : Measure StripSpace) (n : ι → StripSpace) (β : ι → ℝ)
    {w ρ T ε : ℝ} (hε : 0 ≤ ε) (hn : ∀ i, ‖n i‖ = 1) (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hsmall : 4 * w ≤ ρ)
    (hcap : ∀ x : StripSpace,
      μ (Metric.closedBall x (32 * (1 + T) * w / ρ)) ≤ ENNReal.ofReal ε) :
    μ.real (stripFarOverlap n β w ρ T) ≤ (Fintype.card ι : ℝ) ^ 2 * ε := by
  have h := stripFarOverlap_mass_le μ n β hn hT hρ hsmall hcap
  have hr := ENNReal.toReal_mono (by finiteness) h
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hε] using hr

theorem stripParametersClose_of_not_mem_farOverlap {ι : Type*}
    {n : ι → StripSpace} {β : ι → ℝ} {w ρ T : ℝ} {i j : ι} {x : StripSpace}
    (hx : ‖x‖ ≤ T) (hxi : x ∈ affineStrip (n i) (β i) w)
    (hxj : x ∈ affineStrip (n j) (β j) w)
    (hgood : x ∉ stripFarOverlap n β w ρ T) :
    stripParametersClose (n i) (β i) (n j) (β j) ρ := by
  classical
  by_contra hclose
  have hfar : ρ ≤ ‖n i - n j‖ + |β i - β j| ∧
      ρ ≤ ‖n i + n j‖ + |β i + β j| := by
    simp only [stripParametersClose, not_or, not_le] at hclose
    exact ⟨hclose.1.le, hclose.2.le⟩
  apply hgood
  refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, ?_⟩⟩
  simp only [if_pos hfar]
  have hball : x ∈ Metric.closedBall (0 : StripSpace) T := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  exact ⟨⟨hball, hxi⟩, hball, hxj⟩

/-- Any containing representative agrees with a raw prediction at the
second parameter scale, outside the one previously discarded overlap set. -/
theorem raw_strip_prediction_close {ι : Type*}
    {n : ι → StripSpace} {β : ι → ℝ} {w r r₁ r₂ T : ℝ}
    {a : StripSpace} {b : ℝ} {x : StripSpace} {i j : ι}
    (hT : 0 ≤ T) (hx : ‖x‖ ≤ T)
    (hraw : x ∈ affineStrip a b r)
    (hnet : stripParametersClose a b (n j) (β j) r₁)
    (hwidth : r + (1 + T) * r₁ ≤ w)
    (hchosen : x ∈ affineStrip (n i) (β i) w)
    (hgood : x ∉ stripFarOverlap n β w r₂ T) :
    stripParametersClose a b (n i) (β i) (r₁ + r₂) := by
  have hxj : x ∈ affineStrip (n j) (β j) w :=
    (affineStrip_mem_of_close_parameters_mod_sign hT hx hnet hraw).trans hwidth
  exact stripParametersClose_trans hnet
    (stripParametersClose_of_not_mem_farOverlap hx hxj hchosen hgood)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
