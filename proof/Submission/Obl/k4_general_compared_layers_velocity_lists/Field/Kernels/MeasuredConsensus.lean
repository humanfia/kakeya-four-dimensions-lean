-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Kernels.MeasuredConsensus; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Adapted from this LOT tree: obligation o247 (k4_wide_common_field_velocity_lists), branch x0870, commit e81b750b34aa9824cd7568c0d87d020832257f81, file Submission/Obl/k4_wide_common_field_velocity_lists/MeasuredConsensus.lean (session x0870's work). -/
/- Port note: the source file also imported `StateConsensus` and re-exported `real_code_table`,
`stateEntryWeight` and `measurable_state_consensus` as abbreviations; those are the accepted
library's `Submission.Lib.K4OriginalStatePreparation` declarations, which are imported here
instead of copied. Only the three half-state lemmas below are ported. -/
import Submission.Lib.K4OriginalStatePreparation.Measured

namespace Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels

open MeasureTheory Set Finset

noncomputable section

open scoped Classical ENNReal

/-- Keeping at least half of every occupied original state preserves its
palette ceiling with only a factor two. Empty retained states cost zero. -/
theorem half_state_palette {Ω Q V : Type*} [MeasurableSpace Ω]
    (μ current : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure current]
    (state : Ω → Q) (control : Ω → V) (π : V → ℝ) (C : ℝ)
    (hsub : current ≤ μ) (hC : 0 ≤ C) (hπ : ∀ v, 0 ≤ π v)
    (hhalf : ∀ q, current.real (state ⁻¹' {q}) = 0 ∨
      μ.real (state ⁻¹' {q}) / 2 ≤ current.real (state ⁻¹' {q}))
    (hcap : ∀ q v, μ.real {p | state p = q ∧ control p = v} ≤
      C * μ.real (state ⁻¹' {q}) * π v) :
    ∀ q v, current.real {p | state p = q ∧ control p = v} ≤
      2 * C * current.real (state ⁻¹' {q}) * π v := by
  intro q v
  rcases hhalf q with hz | hhalf
  · have hzero : current.real {p | state p = q ∧ control p = v} = 0 :=
      measureReal_mono_null (fun p hp => hp.1) hz
    rw [hzero, hz, mul_zero, zero_mul]
  · have hmono : current.real {p | state p = q ∧ control p = v} ≤
        μ.real {p | state p = q ∧ control p = v} :=
      ENNReal.toReal_mono (measure_ne_top μ _) (hsub _)
    have hstate : μ.real (state ⁻¹' {q}) ≤ 2 * current.real (state ⁻¹' {q}) := by
      linarith
    calc
      _ ≤ C * μ.real (state ⁻¹' {q}) * π v := hmono.trans (hcap q v)
      _ ≤ C * (2 * current.real (state ⁻¹' {q})) * π v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstate hC) (hπ v)
      _ = _ := by ring

/-- The half-state palette transfer in the original extended-real units.
The external palette factor need not be finite or normalized. -/
theorem half_state_palette_ennreal {Ω Q V : Type*} [MeasurableSpace Ω]
    (μ current : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure current]
    (state : Ω → Q) (control : Ω → V) (π : V → ℝ≥0∞) (C : ℝ)
    (hsub : current ≤ μ) (hC : 0 ≤ C)
    (hhalf : ∀ q, current.real (state ⁻¹' {q}) = 0 ∨
      μ.real (state ⁻¹' {q}) / 2 ≤ current.real (state ⁻¹' {q}))
    (hcap : ∀ q v, μ {p | state p = q ∧ control p = v} ≤
      ENNReal.ofReal C * μ (state ⁻¹' {q}) * π v) :
    ∀ q v, current {p | state p = q ∧ control p = v} ≤
      ENNReal.ofReal (2 * C) * current (state ⁻¹' {q}) * π v := by
  intro q v
  rcases hhalf q with hz | hh
  · have hzero : current (state ⁻¹' {q}) = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top current _)).mp hz
    have hevent : current {p | state p = q ∧ control p = v} = 0 :=
      measure_mono_null (fun p hp => hp.1) hzero
    simp only [hevent, hzero, mul_zero, zero_mul, le_refl]
  · have hr : μ.real (state ⁻¹' {q}) ≤ 2 * current.real (state ⁻¹' {q}) := by
      linarith
    have hstate : μ (state ⁻¹' {q}) ≤ 2 * current (state ⁻¹' {q}) := by
      have h := ENNReal.ofReal_le_ofReal hr
      dsimp only [Measure.real] at h
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_toReal (measure_ne_top μ _),
        ENNReal.ofReal_toReal (measure_ne_top current _)] at h
      simpa only [ENNReal.ofReal_ofNat] using h
    calc
      _ ≤ μ {p | state p = q ∧ control p = v} := hsub _
      _ ≤ ENNReal.ofReal C * μ (state ⁻¹' {q}) * π v := hcap q v
      _ ≤ ENNReal.ofReal C * (2 * current (state ⁻¹' {q})) * π v :=
        mul_le_mul' (mul_le_mul' le_rfl hstate) le_rfl
      _ = _ := by
        simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring

/-- Restricting to an original parent that is a function of the original
state retains entire states, so the half-state guarantee is unchanged. -/
theorem parent_restriction_half_states {Ω Q P : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (state : Ω → Q) (parent : Q → P) (H : Set Ω) (p : P)
    (hhalf : ∀ q, μ.real (H ∩ state ⁻¹' {q}) = 0 ∨
      μ.real (state ⁻¹' {q}) / 2 ≤ μ.real (H ∩ state ⁻¹' {q})) :
    ∀ q, μ.real ((H ∩ {x | parent (state x) = p}) ∩ state ⁻¹' {q}) = 0 ∨
      μ.real (state ⁻¹' {q}) / 2 ≤
        μ.real ((H ∩ {x | parent (state x) = p}) ∩ state ⁻¹' {q}) := by
  classical
  intro q
  by_cases hq : parent q = p
  · have heq : (H ∩ {x | parent (state x) = p}) ∩ state ⁻¹' {q} =
        H ∩ state ⁻¹' {q} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · rintro ⟨hx, hs⟩
        exact ⟨⟨hx, by simpa only [hs] using hq⟩, hs⟩
    simpa only [heq] using hhalf q
  · left
    have heq : (H ∩ {x | parent (state x) = p}) ∩ state ⁻¹' {q} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hq ((congrArg parent hx.2).symm.trans hx.1.2)
    simp only [heq, measureReal_empty]

end

end Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels
