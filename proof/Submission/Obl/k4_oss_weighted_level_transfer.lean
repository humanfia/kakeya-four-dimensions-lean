import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_weighted_level_transfer.Transfer
import Submission.Obl.k4_oss_weighted_level_transfer.Discretize
set_option linter.unusedVariables false

/-!
# `Submission.k4_oss_weighted_level_transfer`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_oss_weighted_level_transfer`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_oss_weighted_level_transfer/`
belong to this obligation.
-/

theorem Submission.k4_oss_weighted_level_transfer : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ : ℝ, 0 < γ → γ < 1 → (∃ θ r : ℝ, 0 < θ ∧ 0 < r ∧ r ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < r → ∀ d : ℝ, 0 ≤ d → d ≤ 1 - (γ / 4) → ∀ A B : Finset ℝ, A.Nonempty → B.Nonempty → (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') → (∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a') → (∀ x u : ℝ, δ ≤ u → ((A.filter (fun a => dist a x ≤ u)).card : ℝ) ≤ δ ^ (-θ) * u ^ (s / 2) * (A.card : ℝ)) → (∀ x u : ℝ, δ ≤ u → ((B.filter (fun a => dist a x ≤ u)).card : ℝ) ≤ δ ^ (-θ) * u ^ (s / 2) * (B.card : ℝ)) → δ ^ (θ - d) ≤ (A.card : ℝ) → (A.card : ℝ) ≤ δ ^ (-d - θ) → δ ^ (θ - d) ≤ (B.card : ℝ) → (B.card : ℝ) ≤ δ ^ (-d - θ) → ∀ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-θ) * u ^ (s / 2))) → MeasureTheory.lintegral ν (fun t : ℝ => ENNReal.ofReal (((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ))) ≤ ENNReal.ofReal (δ ^ θ * (A.card : ℝ) ^ 2 * (B.card : ℝ))) → ∃ c ε r : ℝ, 0 < c ∧ 0 < ε ∧ 0 < r ∧ r ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < r → ∀ α ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → MeasureTheory.IsProbabilityMeasure ν → α (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → α (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ (s))) → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (4 * δ ^ (-ε) * u ^ (s))) → ENNReal.ofReal (δ ^ (1 - γ)) ≤ (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} → MeasureTheory.lintegral ν (fun t : ℝ => ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ}) ≤ ENNReal.ofReal (δ ^ c) * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by
  intro s hs hs1 γ hγ hγ1 hgain
  apply Submission.Obl.k4_oss_weighted_level_transfer.conclusion_of_finiteTransfer s γ hs hs1
  apply Submission.Obl.k4_oss_weighted_level_transfer.finite_transfer_of_gain s γ hs hγ
  obtain ⟨θ, r, hθ, hr, hr1, hfinite⟩ := hgain
  exact ⟨θ, r, hθ, hr, hr1, fun δ hδ hδr => hfinite δ hδ hδr⟩
