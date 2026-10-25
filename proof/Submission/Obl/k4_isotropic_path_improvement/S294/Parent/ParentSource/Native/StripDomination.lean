-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripDomination, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripDomination.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripDomination.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripDomination.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripDomination.lean.
   Original comments and attributions are preserved below. -/
import Submission.Lib.K4VelocityStrips

/-! A cellwise likelihood ceiling transfers narrow-strip mass to the unchanged
coarse velocity law, with only one quantization diameter of geometric loss. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

theorem measure_le_smul_of_singleton_caps {Z : Type*} [MeasurableSpace Z]
    [Countable Z] [MeasurableSingletonClass Z]
    (μ ν : Measure Z) (R : ENNReal) (h : ∀ z, μ {z} ≤ R * ν {z}) : μ ≤ R • ν := by
  classical
  apply Measure.le_iff.mpr
  intro S hS
  calc
    μ S = ∑' z, S.indicator (fun z => μ {z}) z :=
      (μ.tsum_indicator_apply_singleton S hS).symm
    _ ≤ ∑' z, R * S.indicator (fun z => ν {z}) z := by
      apply ENNReal.tsum_le_tsum
      intro z
      by_cases hz : z ∈ S
      · simpa only [Set.indicator_of_mem hz] using h z
      · simp only [Set.indicator_of_notMem hz, mul_zero, le_refl]
    _ = R * ν S := by rw [ENNReal.tsum_mul_left, ν.tsum_indicator_apply_singleton S hS]
    _ = (R • ν) S := by rw [Measure.smul_apply, smul_eq_mul]

theorem boundedStrip_measure_eq_of_ae_envelope (μ : Measure StripSpace)
    (n : StripSpace) (β r T : ℝ) (henv : ∀ᵐ x ∂μ, ‖x‖ ≤ T) :
    μ (boundedStrip n β r T) = μ (affineStrip n β r) := by
  apply measure_congr
  filter_upwards [henv] with x hx
  simp only [boundedStrip, mem_inter_iff, Metric.mem_closedBall, dist_zero_right, hx, true_and]

/-- The fine law may be an unnormalized good-state sublaw. Its bin ceilings
are compared against the same coarse law for every bin and every strip. -/
theorem quantized_strip_mass_le {Z : Type*} [MeasurableSpace Z]
    [Countable Z] [MeasurableSingletonClass Z]
    (μ ν : Measure StripSpace) (q : StripSpace → Z) (hq : Measurable q)
    {mesh : ℝ} (hdiam : ∀ x y, q x = q y → ‖x - y‖ ≤ mesh)
    (R : ENNReal) (hbin : ∀ z, μ {x | q x = z} ≤ R * ν {x | q x = z})
    {n : StripSpace} {β r : ℝ} (hn : ‖n‖ = 1) :
    μ (affineStrip n β r) ≤ R * ν (affineStrip n β (r + mesh)) := by
  let B : Set Z := q '' affineStrip n β r
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  have hdom : μ.map q ≤ R • ν.map q := by
    apply measure_le_smul_of_singleton_caps
    intro z
    rw [Measure.map_apply hq (measurableSet_singleton z),
      Measure.map_apply hq (measurableSet_singleton z)]
    exact hbin z
  have hsub : q ⁻¹' B ⊆ affineStrip n β (r + mesh) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hd : ‖x - y‖ ≤ mesh := hdiam x y hxy.symm
    have hi : |inner ℝ (x - y) n| ≤ mesh :=
      (abs_real_inner_le_norm _ _).trans (by simpa only [hn, mul_one] using hd)
    change |inner ℝ x n - β| ≤ _
    have hid : inner ℝ x n - β = (inner ℝ y n - β) + inner ℝ (x - y) n := by
      rw [inner_sub_left]
      ring
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add hy hi)
  calc
    _ ≤ μ (q ⁻¹' B) := measure_mono (fun x hx => ⟨x, hx, rfl⟩)
    _ = μ.map q B := (Measure.map_apply hq hB).symm
    _ ≤ (R • ν.map q) B := Measure.le_iff.mp hdom B hB
    _ = R * ν (q ⁻¹' B) := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hq hB]
    _ ≤ _ := mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le

theorem quantized_bounded_strip_mass_le {Z : Type*} [MeasurableSpace Z]
    [Countable Z] [MeasurableSingletonClass Z]
    (μ ν : Measure StripSpace) (q : StripSpace → Z) (hq : Measurable q)
    {mesh T : ℝ} (hdiam : ∀ x y, q x = q y → ‖x - y‖ ≤ mesh)
    (R : ENNReal) (hbin : ∀ z, μ {x | q x = z} ≤ R * ν {x | q x = z})
    (henv : ∀ᵐ x ∂ν, ‖x‖ ≤ T) {n : StripSpace} {β r : ℝ} (hn : ‖n‖ = 1) :
    μ (affineStrip n β r) ≤ R * ν (boundedStrip n β (r + mesh) T) := by
  rw [boundedStrip_measure_eq_of_ae_envelope ν n β (r + mesh) T henv]
  exact quantized_strip_mass_le μ ν q hq hdiam R hbin hn

/-- A fine strip floor yields a coarse heavy-strip floor against the original
probability palette, with the likelihood cost paid explicitly. -/
theorem heavy_strip_of_quantized_domination {Z : Type*} [MeasurableSpace Z]
    [Countable Z] [MeasurableSingletonClass Z]
    (μ ν : Measure StripSpace) [IsFiniteMeasure ν]
    (q : StripSpace → Z) (hq : Measurable q)
    {mesh T R floor : ℝ} (hR : 0 < R)
    (hdiam : ∀ x y, q x = q y → ‖x - y‖ ≤ mesh)
    (hbin : ∀ z, μ {x | q x = z} ≤ ENNReal.ofReal R * ν {x | q x = z})
    (henv : ∀ᵐ x ∂ν, ‖x‖ ≤ T) {n : StripSpace} {β r : ℝ} (hn : ‖n‖ = 1)
    (hfloor : floor ≤ μ.real (affineStrip n β r)) :
    floor / R ≤ ν.real (boundedStrip n β (r + mesh) T) := by
  have h := quantized_bounded_strip_mass_le μ ν q hq hdiam (ENNReal.ofReal R) hbin henv (β := β) (r := r) hn
  have hreal := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hR.le] at hreal
  apply (div_le_iff₀ hR).mpr
  simpa only [measureReal_def, mul_comm] using hfloor.trans hreal

theorem heavy_strip_of_quantized_domination_real {Z : Type*} [MeasurableSpace Z]
    [Countable Z] [MeasurableSingletonClass Z]
    (μ ν : Measure StripSpace) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (q : StripSpace → Z) (hq : Measurable q)
    {mesh T R floor : ℝ} (hR : 0 < R)
    (hdiam : ∀ x y, q x = q y → ‖x - y‖ ≤ mesh)
    (hbin : ∀ z, μ.real {x | q x = z} ≤ R * ν.real {x | q x = z})
    (henv : ∀ᵐ x ∂ν, ‖x‖ ≤ T) {n : StripSpace} {β r : ℝ} (hn : ‖n‖ = 1)
    (hfloor : floor ≤ μ.real (affineStrip n β r)) :
    floor / R ≤ ν.real (boundedStrip n β (r + mesh) T) := by
  apply heavy_strip_of_quantized_domination μ ν q hq hR hdiam _ henv hn hfloor
  intro z
  have h := ENNReal.ofReal_le_ofReal (hbin z)
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_mul hR.le] using h

/-- This is the form supplied by a fine-history joint ceiling: the selected
strip mass and the cell ceiling both use the original fine-state marginal.
That common marginal cancels once, without renormalizing the selected event. -/
theorem heavy_strip_from_state_joint_cap {Ω Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [Countable Z] [MeasurableSingletonClass Z]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U F : Set Ω)
    (V : Ω → StripSpace) (hV : Measurable V) (q : StripSpace → Z) (hq : Measurable q)
    {mesh T R floor : ℝ} (hR : 0 < R) (hF : 0 < μ.real F)
    (hdiam : ∀ x y, q x = q y → ‖x - y‖ ≤ mesh)
    (hbin : ∀ z, μ.real {x | x ∈ U ∧ x ∈ F ∧ q (V x) = z} ≤
      R * μ.real F * (μ.map V).real {y | q y = z})
    (henv : ∀ᵐ x ∂μ.map V, ‖x‖ ≤ T) {n : StripSpace} {β r : ℝ} (hn : ‖n‖ = 1)
    (hfloor : floor * μ.real F ≤ μ.real {x | x ∈ U ∧ x ∈ F ∧ V x ∈ affineStrip n β r}) :
    floor / R ≤ (μ.map V).real (boundedStrip n β (r + mesh) T) := by
  let fine : Measure StripSpace := (μ.restrict (U ∩ F)).map V
  have happly (S : Set StripSpace) (hS : MeasurableSet S) :
      fine.real S = μ.real {x | x ∈ U ∧ x ∈ F ∧ V x ∈ S} := by
    apply congrArg ENNReal.toReal
    rw [Measure.map_apply hV hS, Measure.restrict_apply (hS.preimage hV)]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    tauto
  have hcap : ∀ z, fine.real {y | q y = z} ≤
      (R * μ.real F) * (μ.map V).real {y | q y = z} := by
    intro z
    rw [happly _ (measurableSet_eq_fun hq measurable_const)]
    exact hbin z
  have hlow : floor * μ.real F ≤ fine.real (affineStrip n β r) := by
    rw [happly _ (measurableSet_affineStrip _ _ _)]
    exact hfloor
  have h := heavy_strip_of_quantized_domination_real fine (μ.map V) q hq
    (mul_pos hR hF) hdiam hcap henv hn hlow
  have he : (floor * μ.real F) / (R * μ.real F) = floor / R := by
    field_simp
  rwa [he] at h

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
