import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Statement

/-!
# The row fit on one block (Part I of the first jet): statement

Paper Proposition 5.4, "Fitting one row component": on a time block `[t₀, t₀ + H]` carrying
labeled incidence mass `≥ λ H`, with instantaneous labeled mass `≥ λ` at each labeled time,
the planar dot-product alternative (`WangZahlLot.wz_ad_projection_dichotomy`) fits one
component of the time-only row `F` by an affine function with error `N^ε₁ H^(5/4)` on a set of
labeled times of length `≥ N^(-ε₁) H`.

`RowFitComponent` is that statement for the data of `FirstJet.Data`; applying it to both
components (the second time to the labels restricted to the first fitting set) gives the
affine row used by the residual-slope concentration. The block length ranges over
`N^(-c'') ≤ H ≤ N^(-c')` with `ζ ≤ H^8`, which contains the length `≍ w^(64/(1-d))` used by the
cover; the lower bound `N^(-c'')` lets the planar loss `p^ε` (with `p = H^(1/4)`) be absorbed
into `N^(-ε₁)`.
-/

open MeasureTheory

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

/-- The labeled prior mass at a time. -/
def timeMass {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (E : Set (Ω × ℝ)) (t : ℝ) :
    ENNReal :=
  ν {l | (l, t) ∈ E}

/-- Part I of the first jet for one row component `i`: for every `d < 1`, powers
`0 < c' ≤ c''` bounding the block length and loss `ε₁ > 0`, small hypothesis losses `N^η`
and large `N` give, on every block of length `N^(-c'') ≤ H ≤ N^(-c')`, `ζ ≤ H^8`, whose labeled
mass is `≥ N^(-η) H` and whose labeled times all carry mass `≥ N^(-η)`, a set `T` of labeled
times in the block of length `≥ N^(-ε₁) H` on which `F i` is affine up to `N^ε₁ H^(5/4)`. -/
def RowFitComponent : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c' c'' : ℝ, 0 < c' → c' ≤ c'' → ∀ ε₁ : ℝ, 0 < ε₁ →
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
      ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ) (ζ : ℝ),
        0 < ζ → Data ν y β γ E F d (N ^ η) ζ →
      ∀ (H t₀ : ℝ), N ^ (-c'') ≤ H → H ≤ N ^ (-c') → ζ ≤ H ^ 8 → 0 ≤ t₀ → t₀ + H ≤ 1 →
        ENNReal.ofReal (N ^ (-η) * H) ≤
          (ν.prod volume) (E ∩ Set.univ ×ˢ Set.Icc t₀ (t₀ + H)) →
        (∀ t ∈ Set.Icc t₀ (t₀ + H), (∃ l, (l, t) ∈ E) →
          ENNReal.ofReal (N ^ (-η)) ≤ timeMass ν E t) →
      ∀ i : Fin 2, ∃ T : Set ℝ, MeasurableSet T ∧ T ⊆ Set.Icc t₀ (t₀ + H) ∧
        (∀ t ∈ T, ∃ l, (l, t) ∈ E) ∧
        ENNReal.ofReal (N ^ (-ε₁) * H) ≤ volume T ∧
        ∃ a A : ℝ, |A| ≤ N ^ ε₁ ∧ ∀ t ∈ T, |F t i - (a + (t - t₀) * A)| ≤
          N ^ ε₁ * H ^ (5 / 4 : ℝ)

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
