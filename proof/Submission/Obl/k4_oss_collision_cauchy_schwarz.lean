import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_collision_cauchy_schwarz.Mixture
import Submission.Obl.k4_oss_collision_cauchy_schwarz.Rearrange
set_option linter.unusedVariables false

/-!
# `Submission.k4_oss_collision_cauchy_schwarz`

Condition on the two beta variables, apply the interval-cell collision inequality
for a mixture, and rearrange the four independent alpha variables.
-/

open MeasureTheory
open scoped ENNReal

namespace Submission.Obl.k4_oss_collision_cauchy_schwarz

theorem _root_.Submission.k4_oss_collision_cauchy_schwarz : ∀ δ : ℝ, 0 < δ → ∀ α β : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → MeasureTheory.IsProbabilityMeasure β → ∀ ω : MeasureTheory.Measure ℝ, ω = MeasureTheory.Measure.map (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q.1.1 * q.1.2 - q.2.1 * q.2.2) / 4) ((α.prod β).prod (α.prod β)) → (ω.prod ω) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ≤ 3 * MeasureTheory.lintegral (β.prod β) (fun p : ℝ × ℝ => ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) | |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ}) := by
  intro δ hδ α β hα hβ ω hω
  let : IsProbabilityMeasure α := hα
  let : IsProbabilityMeasure β := hβ
  let f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    fun q => (q.2.1 * q.1.1 - q.2.2 * q.1.2) / 4
  have hf : Measurable f := by fun_prop
  have hT : MeasurePreserving
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((q.1.2, q.2.2), (q.1.1, q.2.1)))
      ((α.prod β).prod (α.prod β)) ((β.prod β).prod (α.prod α)) :=
    Measure.measurePreserving_swap.comp (measurePreserving_pair_transpose α β α β)
  have hν : Measure.map f ((β.prod β).prod (α.prod α)) = ω := by
    rw [hω, ← hT.map_eq, Measure.map_map hf hT.measurable]
    rfl
  have htranspose := measurePreserving_pair_transpose α α α α
  have hpoint (p : ℝ × ℝ) :
      ((α.prod α).prod (α.prod α))
        {q : (ℝ × ℝ) × (ℝ × ℝ) | |f (p, q.1) - f (p, q.2)| ≤ δ} =
      ((α.prod α).prod (α.prod α))
        {q : (ℝ × ℝ) × (ℝ × ℝ) |
          |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ} := by
    have hs : MeasurableSet {q : (ℝ × ℝ) × (ℝ × ℝ) |
        |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ} := by
      measurability
    have hset :
        {q : (ℝ × ℝ) × (ℝ × ℝ) | |f (p, q.1) - f (p, q.2)| ≤ δ} =
        (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ((q.1.1, q.2.1), (q.1.2, q.2.2))) ⁻¹'
        {q : (ℝ × ℝ) × (ℝ × ℝ) |
          |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ} := by
      ext q
      change |(q.1.1 * p.1 - q.1.2 * p.2) / 4 -
          (q.2.1 * p.1 - q.2.2 * p.2) / 4| ≤ δ ↔
        |p.1 * (q.1.1 - q.2.1) - p.2 * (q.1.2 - q.2.2)| ≤ 4 * δ
      rw [show (q.1.1 * p.1 - q.1.2 * p.2) / 4 -
          (q.2.1 * p.1 - q.2.2 * p.2) / 4 =
          (p.1 * (q.1.1 - q.2.1) - p.2 * (q.1.2 - q.2.2)) / 4 by ring,
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
      rw [mul_comm δ 4]
    rw [hset]
    exact htranspose.measure_preimage hs.nullMeasurableSet
  have h := collision_mixture_le (β.prod β) (α.prod α) f hf hδ
  dsimp only at h
  rw [hν] at h
  simpa only [hpoint] using h

end Submission.Obl.k4_oss_collision_cauchy_schwarz
