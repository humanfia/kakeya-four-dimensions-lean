import Submission.Obl.k4_scalar_grid_cartesian_field.PacketGeometry

/-!
# The packet-level Cartesian field core (interface)

`CartesianCoreStatement M` is the single-packet heart of o230 (paper §6,
"Cartesian interpolation of the physical field", with the qualification
degree `M`): inside one depth-1 packet `A` with block `Icc a (a + h)`, a
measurable incidence set `S₀ ⊆ E ∩ (A × block)` whose incidences are all
qualified, with fine-cube palette breadth, a base-density ceiling and the
coarse graph lists of the velocity graph `G`, carries a polynomial field `𝒯`
(degree `≤ 2M`, coefficients `≤ C Λ^q`) and a measurable `S₁ ⊆ S₀` of mass
`≥ ρ S₀ / (C Λ^q)` on whose lines the frozen field comparison holds
throughout the block, with error `C Λ^q εT`.

`Λ ≥ 1` is one budget dominating every subpower loss of the input. All the
objects are written exactly as in the frozen statement: `physCube N r` is the
frozen `phys k r`, `rowBin N r` the frozen `rowbin k r`.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set MvPolynomial

/-- The frozen floor-grid `(t, y, X)` cube `phys k r` of side `N ^ (-r)`. -/
noncomputable def physCube (N r : ℝ) (p : Incidence) : Fin 3 → ℤ :=
  fun e => ⌊(![p.2, scalarY p.1 p.2, scalarX p.1 p.2] : Fin 3 → ℝ) e / N ^ (-r)⌋

/-- The frozen row bin `rowbin k r` of width `N ^ (-r)`. -/
noncomputable def rowBin (N r : ℝ) (w : Fin 2 → ℝ) : Fin 2 → ℤ :=
  fun e => ⌊w e / N ^ (-r)⌋

/-- The frozen field residual `X'(t) - 𝒯(u(t)) · (1, V)` of a line, in the
normalized base coordinates `u = ((t, y) - z₀) / h`. -/
noncomputable def coreResidual (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (h : ℝ)
    (z₀ : Fin 2 → ℝ) (l : Trajectory) (t : ℝ) : ℝ :=
  l.2 3 + 2 * t * l.2 4 - ∑ e : Fin 2, MvPolynomial.eval
    (fun e : Fin 2 => ((![t, scalarY l t] : Fin 2 → ℝ) e - z₀ e) / h) (𝒯 e) *
      (![1, l.2 1] : Fin 2 → ℝ) e

/-- The packet-level Cartesian field core. -/
def CartesianCoreStatement (M : ℕ) : Prop :=
  ∃ (C : ℝ) (q q₀ : ℕ), 0 < C ∧
  ∀ (N Λ h a y₀ εT rT B L ξ δv δs : ℝ)
    (ρ : Measure Incidence) (θ ν : Measure Trajectory) (π : Measure ℝ)
    (E S₀ : Set Incidence) (A : Set Trajectory) (G : (Fin 3 → ℤ) → Fin 2 → ℝ),
    -- scalars
    2 ≤ N → 1 ≤ Λ → 0 < h → h ≤ 1 → 0 ≤ a → a + h ≤ 1 →
    εT = N ^ (-rT) → 0 < ξ → 0 < δv → 0 < δs →
    -- scale constraints: `εT` subpower-small, fit and graph precision, thin layer,
    -- small cells, narrow velocity bins, tiny fine cubes, conditioned directions
    C * Λ ^ q₀ * εT ≤ 1 → h ^ M ≤ εT → Λ * N ^ (-L) ≤ εT →
    Λ ^ 2 * N ^ (-(1 : ℝ)) ≤ εT →
    Λ ^ 4 * ξ ≤ εT →
    Λ ^ 2 * δv ≤ ξ →
    Λ ^ 4 * N ^ (-B) ≤ ξ * h →
    1 ≤ Λ * δs → δs ≤ 1 →
    -- measures
    IsFiniteMeasure ρ → IsFiniteMeasure θ → SigmaFinite ν → IsProbabilityMeasure π →
    MeasurableSet E → MeasurableSet S₀ → MeasurableSet A →
    S₀ ⊆ E → S₀ ⊆ {p | p.1 ∈ A ∧ p.2 ∈ Icc a (a + h)} →
    0 < ρ S₀ →
    ρ.restrict S₀ ≤ ENNReal.ofReal Λ • ν.prod volume →
    ENNReal.ofReal h * ν A ≤ ENNReal.ofReal Λ * ρ S₀ →
    -- two-sided incidence density on the graph set (prepData)
    (θ.prod volume).restrict E ≤ ENNReal.ofReal Λ • ρ.restrict E →
    ρ.restrict E ≤ ENNReal.ofReal Λ • (θ.prod volume).restrict E →
    -- packet geometry: bounded coefficients, base confinement, Lipschitz hidden layer
    (∀ l ∈ A, ∀ e, |l.2 e| ≤ Λ) →
    (∀ l ∈ A, ∀ t ∈ Icc a (a + h), |scalarY l t - y₀| ≤ Λ * h) →
    (∀ l ∈ A, ∀ l' ∈ A, ∀ t ∈ Icc a (a + h), ∀ t' ∈ Icc a (a + h),
      |scalarX l t - scalarX l' t'| ≤
        Λ * N ^ (-(1 : ℝ)) + Λ / h * (|t - t'| + |scalarY l t - scalarY l' t'|)) →
    -- the velocity graph on fine `B`-cubes
    (∀ p ∈ E, (∀ e, |G (physCube N B p) e| ≤ Λ) ∧
      |p.1.2 3 + 2 * p.2 * p.1.2 4 - G (physCube N B p) 0 -
        G (physCube N B p) 1 * p.1.2 1| ≤ Λ * N ^ (-L)) →
    -- its coarse row lists at width `εT`
    (∀ q : Fin 3 → ℤ, ({w : Fin 2 → ℤ | ρ.restrict E
      {p | physCube N rT p = q ∧ rowBin N rT (G (physCube N B p)) = w} ≠ 0}.ncard : ℝ) ≤ Λ) →
    -- velocity breadth in fine cubes at the separation width `δs`
    (∀ (q : Fin 3 → ℤ) (c : ℤ),
      16 * ρ.restrict S₀ {p | physCube N B p = q ∧ ⌊p.1.2 1 / δs⌋ = c} ≤
        ρ.restrict S₀ {p | physCube N B p = q}) →
    -- palette domination in fine cubes at the narrow width `δv`
    (∀ (q : Fin 3 → ℤ) (c : ℤ),
      ρ.restrict S₀ {p | physCube N B p = q ∧ ⌊p.1.2 1 / δv⌋ = c} ≤
        ENNReal.ofReal Λ * ρ.restrict S₀ {p | physCube N B p = q} *
          π {w | ⌊w / δv⌋ = c}) →
    -- every incidence of `S₀` is qualified (degree `M`)
    (∀ p ∈ S₀, ∃ P : Fin 2 → Polynomial ℝ,
      (∀ e, (P e).natDegree ≤ M ∧ ∀ i, |(P e).coeff i| ≤ Λ) ∧
      (∀ e, |G (physCube N B p) e - (P e).eval p.2| ≤ h ^ M) ∧
      ENNReal.ofReal (h / Λ) ≤ volume {t | (p.1, t) ∈ E ∧ t ∈ Icc a (a + h) ∧
        ∀ e, |G (physCube N B (p.1, t)) e - (P e).eval t| ≤ h ^ M}) →
    -- base-density ceiling at width `ξ` in normalized coordinates
    (∀ c : Fin 2 → ℤ, ρ.restrict S₀
      {p | ∀ e, ⌊normalizedBase h ![a, y₀] p e / ξ⌋ = c e} ≤
        ENNReal.ofReal (Λ * ξ ^ 2) * ρ S₀) →
    ∃ (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (S₁ : Set Incidence),
      MeasurableSet S₁ ∧ S₁ ⊆ S₀ ∧
      (∀ e, (𝒯 e).totalDegree ≤ 2 * M) ∧
      (∀ e b, |(𝒯 e).coeff b| ≤ C * Λ ^ q) ∧
      ENNReal.ofReal (1 / (C * Λ ^ q)) * ρ S₀ ≤ ρ S₁ ∧
      ∀ p ∈ S₁, ∀ t ∈ Icc a (a + h),
        |coreResidual 𝒯 h ![a, y₀] p.1 t| ≤ C * Λ ^ q * εT

end Submission.Obl.k4_scalar_grid_cartesian_field
