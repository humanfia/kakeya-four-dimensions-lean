import Submission.Obl.k4_oss_grid_rounding.Grid
import Submission.Obl.k4_oss_grid_rounding.Transfer
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.k4_oss_grid_rounding`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_oss_grid_rounding`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_oss_grid_rounding/`
belong to this obligation.
-/

namespace Submission.Obl.k4_oss_grid_rounding

theorem _root_.Submission.k4_oss_grid_rounding : ∀ δ : ℝ, 0 < δ → δ < (1 / 2 : ℝ) → ∀ α : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → α (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → ∃ (F : Finset ℝ) (p : ℝ → ℝ), (∀ x ∈ F, 0 ≤ p x) ∧ Finset.sum F p = 1 ∧ (∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ dist x y) ∧ (F.card : ℝ) ≤ 4 / δ ∧ 0 < Finset.sum F (fun x => p x ^ 2) ∧ ENNReal.ofReal (Finset.sum F (fun x => p x ^ 2)) ≤ (α.prod α) {q : ℝ × ℝ | |q.1 - q.2| ≤ δ} ∧ (α.prod α) {q : ℝ × ℝ | |q.1 - q.2| ≤ δ} ≤ ENNReal.ofReal (3 * (Finset.sum F (fun x => p x ^ 2))) ∧ (∀ x u : ℝ, δ ≤ u → ENNReal.ofReal (Finset.sum (F.filter (fun y => dist y x ≤ u)) p) ≤ α (Set.Icc (x - 2 * u) (x + 2 * u))) ∧ (∀ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 → MeasureTheory.lintegral ν (fun t : ℝ => ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ}) ≤ MeasureTheory.lintegral ν (fun t : ℝ => Finset.sum (((F.product F).product (F.product F)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |(q.1.1 - 2 * t * q.1.2) - (q.2.1 - 2 * t * q.2.2)| ≤ 7 * δ)) (fun q => ENNReal.ofReal (p q.1.1 * p q.1.2 * p q.2.1 * p q.2.2)))) := by
  intro δ hδ hδhalf α hα hsupp
  have : MeasureTheory.IsProbabilityMeasure α := hα
  obtain ⟨hlower, hupper⟩ := energy_comparison hδ α hsupp
  refine ⟨grid δ, weight δ α, fun y _ => weight_nonneg δ α y,
    sum_weight hδ α hsupp, grid_separated hδ, grid_card_le hδ hδhalf,
    sum_weight_sq_pos hδ α hsupp, hlower, hupper, weighted_ball hδ α, ?_⟩
  intro ν hν hνsupp
  exact fourfold_transfer α (rounding δ) (measurable_rounding δ) (grid δ)
    (rounding_ae_mem hδ α hsupp)
    (fun x => by simpa only [Real.dist_eq] using rounding_dist hδ x)
    (weight δ α) (fun y hy => rfl) ν hνsupp

end Submission.Obl.k4_oss_grid_rounding
