-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.FinalTune, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The final tuning and the eventual lanes (session x1088).

* `finalTune`: the Tuning of the relative source: depth and budget of x1096's `NativeDesign`, slack
  `max FixedSourcePowers.slack censusSlack` (paying the core/jet powers, x1095, and the census
  powers, `Source.CensusEventual`).
* `LanesEventually tune`: after the pre-sample choices of `StagesProducer`, the lanes
  (`Source.SampleAt.LanesAt`) hold eventually, uniformly for every path exponent `σ ≤ σL` — the
  statement x1082's lane assembly proves, and the outer assembly consumes. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleAt

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- **The final tuning.** -/
def finalTune : Tuning where
  depth := NativeDesign.depth
  budget := NativeDesign.budget
  one_le_depth := NativeDesign.one_le_depth
  budget_pos := NativeDesign.budget_pos
  budget_le_one := NativeDesign.budget_le_one
  slack := max FixedSourcePowers.slack censusSlack
  one_le_slack := one_le_censusSlack.trans (le_max_right _ _)

theorem finalTune_slack : FixedSourcePowers.slack ≤ finalTune.slack := le_max_left _ _

theorem finalTune_censusSlack : censusSlack ≤ finalTune.slack := le_max_right _ _

theorem finalTune_depth (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    finalTune.depth κ₁ d₁ Ep precision loss = NativeDesign.depth κ₁ d₁ Ep precision loss := rfl

theorem finalTune_budget (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    finalTune.budget κ₁ d₁ Ep precision loss = NativeDesign.budget κ₁ d₁ Ep precision loss := rfl

/-- **The lanes hold eventually**, uniformly in the path exponent below `σL`. -/
def LanesEventually (tune : Tuning) : Prop :=
  O204.Split.mk →
  ∀ (d₁ κ₁ ρ : ℝ) (Ep : ℕ) (precision loss e0 : ℝ),
  0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < ρ → d₁ + ρ < 1 → 1 ≤ precision → 0 < loss →
  loss ≤ 1 → 0 < e0 →
  ∀ (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (C target : ℕ) (indices : Finset ℕ),
  Parent.grid κ₁ ρ m s (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀
      (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) / 8) →
  δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) →
  4 * δ₀ * (m : ℝ) ≤ κ₁ → 8 ≤ m →
  8 ≤ gridFineOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m →
  target < m → s target = 1 / 2 → 2 * (target + 1) = m → 1 ≤ C →
  windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m ≤ C →
  (C : ℝ) ≤ windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m + 1 →
  C + 1 ≤ target → indices = Finset.range (target + 1 - C) →
  ∀ (d : Parent.ParentSource.Native.ProblemData), d.Valid →
  (∀ r : ℝ, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L) →
  ∀ (Mp Dp : ℕ) (budget : ℝ), 0 < budget → budget ≤ 1 →
  ∃ σL : ℝ, 0 < σL ∧ ∀ᶠ k in atTop, ∀ σ : ℝ, 0 < σ → σ ≤ σL →
    LanesAt tune d₁ κ₁ Ep precision loss e0 m s δ₀ C indices d Mp Dp budget k σ

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
