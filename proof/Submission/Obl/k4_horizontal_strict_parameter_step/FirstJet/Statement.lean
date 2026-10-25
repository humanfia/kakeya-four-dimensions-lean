import Submission.Obl.k4_fixed_prior_chart_regularization.FirstJetStatement

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/FirstJet/Statement.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

/-!
# The first-jet cover: statement

The scalar-normal first jet (paper Proposition 5.4, `prop:scalar-normal`) in the case used by
the interior bootstrap: static tangential coordinates `y_l ∈ ℝ²` and affine normalized scalars
`x̄_l(t) = β_l + t γ_l`. With a time-only row `F(t)` put
`S_l(t) = x̄_l(t) - F(t) · y_l`.

Hypotheses, with `K = N ^ η`, a reading width `w = N ^ (-c)` and the floor
`ζ = w ^ (1000 / (1 - d))`, at every resolution `ζ ≤ q ≤ r ≤ 1`:

* `support`: at every time, the labeled scalar values in any interval of length `r` meet at most
  `K (r/q)^d` cells of width `q`;
* `absCap`: the labeled prior mass of a `q`-cell of `(x̄_l(t), y_l)` is at most `K q^(2+d)`;
* `rowLip`: `|F(t) - F(u)| ≤ K (|t-u| + ζ)` at active times;
* `slopeLip`: `|γ_l - γ_l'| ≤ K (spacetime distance + ζ)` between labeled points;
* `binCap`: relative to a coefficient bin of dyadic side `r = 2^(-n)` of `(y, β, γ)`, a `q`-cell
  has relative labeled prior mass at most `K (q/r)^(2+d)`.

Conclusion (`FirstJetCover`): one time `t*`, one row `A` and a set of trajectories `L` carrying
labeled incidence mass `≥ N^(-ε)`, on which the pairs of cells
`(S_l(t*)_w, (γ_l - A · y_l)_w)` take at most `N^ε w^(-d)` values. This is exactly what
`jet_cover_to_family` (x0852, `JetFamilies.lean`) turns into full-time predictors.
-/

open MeasureTheory

noncomputable section

namespace Submission.Obl.k4_horizontal_strict_parameter_step.FirstJet

/-- The normalized scalar `x̄_l(t) = β_l + t γ_l`. -/
def xbar {Ω : Type*} (β γ : Ω → ℝ) (l : Ω) (t : ℝ) : ℝ := β l + t * γ l

/-- The scalar `S_l(t) = x̄_l(t) - F(t) · y_l`. -/
def scal {Ω : Type*} (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ) (l : Ω) (t : ℝ) :
    ℝ :=
  xbar β γ l t - (F t 0 * y l 0 + F t 1 * y l 1)

/-- The hypotheses of the first-jet cover at one resolution floor `ζ` and constant `K`. -/
abbrev Data {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (y : Ω → Fin 2 → ℝ)
    (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ) (d K ζ : ℝ) : Prop :=
  Submission.Obl.k4_fixed_prior_chart_regularization.FirstJet.Data ν y β γ E F d K ζ

/-- The first-jet cover at reading width `w`, loss `N^ε`. -/
def Cover {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (y : Ω → Fin 2 → ℝ)
    (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ) (d N ε w : ℝ) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ A : Fin 2 → ℝ, (∀ i, |A i| ≤ N ^ ε) ∧
    ∃ L : Set Ω, MeasurableSet L ∧
      ENNReal.ofReal (N ^ (-ε)) ≤ (ν.prod volume) (E ∩ L ×ˢ Set.univ) ∧
      ∃ P : Finset (ℤ × ℤ), (P.card : ℝ) ≤ N ^ ε * w ^ (-d) ∧
        ∀ l ∈ L, (⌊scal y β γ F l t / w⌋, ⌊(γ l - (A 0 * y l 0 + A 1 * y l 1)) / w⌋) ∈ P

/-- The first-jet cover theorem: for every `d < 1`, reading exponent `c > 0` and loss `ε > 0`,
small enough hypothesis losses `N^η` and large `N` give the cover at `w = N^(-c)` from the data
at the floor `ζ = w^(1000/(1-d))`. -/
def FirstJetCover : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω), IsProbabilityMeasure ν →
      ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ),
        Data ν y β γ E F d (N ^ η) ((N ^ (-c)) ^ (1000 / (1 - d))) →
        Cover ν y β γ E F d N ε (N ^ (-c))

end Submission.Obl.k4_horizontal_strict_parameter_step.FirstJet

end
