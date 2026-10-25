import Submission.Obl.k4_raw_critical_segment_forests.Preparation

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

/-- The strengthened induction statement allows any finite positive prefix,
including prefixes whose final target lies before one. -/
def PrefixConstruction : Prop :=
  Preparation → Composition → Initial →
  ∀ ds kr S η w : ℝ, Extremal ds kr S η → 0 ≤ w → UniformWidth ds kr S η w →
  ∀ (m : ℕ) (s : ℕ → ℝ), 0 < m →
    (∀ i, i < m → 0 < s i ∧ s i ≤ 1) →
    (∀ i, i + 1 < m → s i < s (i + 1)) →
    ∀ ε q : ℝ, 0 < ε → ε ≤ 1 → 0 < q →
    ∃ t : ℝ, 0 < t ∧ ∀ p : Data, Valid p → p.L = 1 → p.S = S → p.η = η →
      p.d < ds + t → kr - t < Horizon p →
      ∃ (r : ℕ → ℝ) (M D : ℕ),
        (∀ i, i < m → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ s i ∧ (s i = 1 → r i = 1)) ∧
        ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop, RawAt p kr w ε q σ m s r M D k

end Submission.Obl.k4_raw_critical_segment_forests
