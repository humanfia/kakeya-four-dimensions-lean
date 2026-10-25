import Mathlib

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

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

/-- The normalized scalar `x̄_l(t) = β_l + t γ_l`. -/
def xbar {Ω : Type*} (β γ : Ω → ℝ) (l : Ω) (t : ℝ) : ℝ := β l + t * γ l

/-- The scalar `S_l(t) = x̄_l(t) - F(t) · y_l`. -/
def scal {Ω : Type*} (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ) (l : Ω) (t : ℝ) :
    ℝ :=
  xbar β γ l t - (F t 0 * y l 0 + F t 1 * y l 1)

/-- The hypotheses of the first-jet cover at one resolution floor `ζ` and constant `K`. -/
structure Data {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (y : Ω → Fin 2 → ℝ)
    (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ) (d K ζ : ℝ) : Prop where
  measurable_y : Measurable y
  measurable_β : Measurable β
  measurable_γ : Measurable γ
  measurable_F : Measurable F
  measurableSet_E : MeasurableSet E
  subset_E : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1
  bound_y : ∀ l i, |y l i| ≤ K
  bound_β : ∀ l, |β l| ≤ K
  bound_γ : ∀ l, |γ l| ≤ K
  bound_F : ∀ t i, |F t i| ≤ K
  mass : ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E
  support : ∀ t q r a : ℝ, ζ ≤ q → q ≤ r → r ≤ 1 →
    ∃ C : Finset ℤ, (C.card : ℝ) ≤ K * (r / q) ^ d ∧
      ∀ l, (l, t) ∈ E → a ≤ scal y β γ F l t → scal y β γ F l t ≤ a + r →
        ⌊scal y β γ F l t / q⌋ ∈ C
  absCap : ∀ t q : ℝ, ζ ≤ q → q ≤ 1 → ∀ z : Fin 3 → ℤ,
    ν {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} ≤
      ENNReal.ofReal (K * q ^ (2 + d))
  rowLip : ∀ t u : ℝ, (∃ l, (l, t) ∈ E) → (∃ l, (l, u) ∈ E) → ∀ i,
    |F t i - F u i| ≤ K * (|t - u| + ζ)
  slopeLip : ∀ l l' t u, (l, t) ∈ E → (l', u) ∈ E →
    |γ l - γ l'| ≤ K * (|t - u| + |xbar β γ l t - xbar β γ l' u| + |y l 0 - y l' 0| +
      |y l 1 - y l' 1| + ζ)
  binCap : ∀ (q : ℝ) (n : ℕ), ζ ≤ q → q ≤ (2 : ℝ) ^ (-(n : ℤ)) → ∀ (b : Fin 4 → ℤ) (t : ℝ)
    (z : Fin 3 → ℤ),
    ν {l | (⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧
        ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3) ∧
        (l, t) ∈ E ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} ≤
      ENNReal.ofReal (K * (q / (2 : ℝ) ^ (-(n : ℤ))) ^ (2 + d)) *
        ν {l | ⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧
          ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3}

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

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
