import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_finite_energy_relation
import Submission.Obl.k4_oss_bad_direction_extraction
import Submission.Obl.k4_oss_weighted_level_transfer
import Submission.Obl.k4_oss_projection_flattening.Slope
import Submission.Obl.k4_oss_projection_flattening.FiniteGain
set_option linter.unusedVariables false

/-!
# `Submission.k4_oss_projection_flattening`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_oss_projection_flattening`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_oss_projection_flattening/`
belong to this obligation.
-/

theorem Submission.k4_oss_projection_flattening : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ c ε δ₀ : ℝ, 0 < c ∧ 0 < ε ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ α β : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → MeasureTheory.IsProbabilityMeasure β → α (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → β (Set.Icc (1 : ℝ) 2)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → α (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → β (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) → ENNReal.ofReal (δ ^ (1 - γ)) ≤ (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} → MeasureTheory.lintegral (β.prod β) (fun p : ℝ × ℝ => ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) | |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ}) ≤ ENNReal.ofReal (δ ^ c) * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} := by
  intro s hs hs1 γ hγ hγ1
  have hfinite : Submission.Obl.k4_oss_projection_flattening.FiniteEnergyGain
      (s / 2) (γ / 4) :=
    Submission.Obl.k4_oss_projection_flattening.finite_energy_gain
      (Submission.k4_oss_bad_direction_extraction Submission.k4_oss_finite_energy_relation)
      (s / 2) (γ / 4) (by linarith) (by linarith) (by linarith)
  obtain ⟨c, ε, r, hc, hε, hr, hr1, hweighted⟩ :=
    Submission.k4_oss_weighted_level_transfer s hs hs1 γ hγ hγ1 hfinite
  refine ⟨c, ε, r, hc, hε, hr, ?_⟩
  intro δ hδ hδr α β hα hβ hαsupp hβsupp hαF hβF hQ
  have : MeasureTheory.IsProbabilityMeasure β := hβ
  obtain ⟨ν, hν, hνsupp, hνF, hcompare⟩ :=
    Submission.Obl.k4_oss_projection_flattening.ratio_direction_law s ε δ hs hs1 hε hδ
      (hδr.le.trans hr1) β hβsupp hβF
  exact (hcompare α hα).trans
    (hweighted δ hδ hδr α ν hα hν hαsupp hνsupp hαF hνF hQ)
