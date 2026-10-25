import Submission.Obl.k4_finite_width_output_exclusion.Horizon

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Below the true horizon, systems of any fixed format are eventually
excluded at some positive slack tolerance. -/
lemma eventually_no_short_true_atlas {p : Data} (hp : Valid p) {h : ℝ}
    (hh : h < Horizon p) (M D : ℕ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ k in atTop, ∀ (κ : ℝ) (a : Atlas p k),
      1 ≤ κ → p.K k ≤ κ → κ ≤ p.N k ^ τ → a.TrueAt M D κ →
      p.N k ^ h < (2 : ℝ) ^ a.T := by
  classical
  have hn : ¬ Cost p h := fun hc => (not_le_of_gt hh) (horizon_le_cost hp hc)
  have hfixed : ¬ ∀ τ : ℝ, 0 < τ → ∃ᶠ k in atTop,
      ∃ κ : ℝ, 1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ τ ∧
        ∃ a : Atlas p k, (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.TrueAt M D κ := by
    intro hfixed
    exact hn ((cost_iff p h).2 ⟨M, D, hfixed⟩)
  obtain ⟨τ, hfixed⟩ := not_forall.mp hfixed
  obtain ⟨hτ, hfixed⟩ := not_imp.mp hfixed
  have hlate := not_frequently.mp hfixed
  refine ⟨τ, hτ, hlate.mono ?_⟩
  intro k hk κ a hκ hKκ hκτ ha
  by_contra hbad
  exact hk ⟨κ, hκ, hKκ, hκτ, a, le_of_not_gt hbad, ha⟩

end
end Submission.Obl.k4_raw_critical_segment_forests
