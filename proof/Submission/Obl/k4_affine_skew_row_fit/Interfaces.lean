import Mathlib

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_affine_skew_row_fit

abbrev Edge := (ℝ × ℝ) × (ℝ × ℝ)

/-- The finite planar data in Assumption 7.2, with one explicit loss factor. -/
structure PlanarGraphData (h K S : ℝ) where
  size : ℕ
  weight : Fin size → ℝ
  ratio : Fin size → ℝ
  left : Finset (ℝ × ℝ)
  right : Finset (ℝ × ℝ)
  graph : Fin size → Finset Edge
  left_grid : ∀ x ∈ left, ∃ a b : ℤ, x = (h * a, h * b)
  right_grid : ∀ y ∈ right, ∃ a b : ℤ, y = (h * a, h * b)
  left_bound : ∀ x ∈ left, |x.1| ≤ K ∧ |x.2| ≤ K
  right_bound : ∀ y ∈ right, |y.1| ≤ K ∧ |y.2| ≤ K
  left_card_lower : 1 / (K * h) ≤ (left.card : ℝ)
  left_card_upper : (left.card : ℝ) ≤ K / h
  right_card_lower : 1 / (K * h) ≤ (right.card : ℝ)
  right_card_upper : (right.card : ℝ) ≤ K / h
  weight_nonneg : ∀ i, 0 ≤ weight i
  sum_weight : (∑ i, weight i) = 1
  ratio_bound : ∀ i, 1 / K ≤ |ratio i| ∧ |ratio i| ≤ K
  ratio_cap : ∀ x r : ℝ, h ≤ r → r ≤ 1 →
    (∑ i, if ratio i ∈ Icc x (x + r) then weight i else 0) ≤ K * r ^ S
  graph_subset : ∀ i, graph i ⊆ left ×ˢ right
  graph_card : ∀ i, 1 / (K * h ^ 2) ≤ ((graph i).card : ℝ)
  sum_card : ∀ i,
    (((graph i).image (fun p : Edge =>
      (⌊(p.1.1 + ratio i * p.2.1) / h⌋,
        ⌊(p.1.2 + ratio i * p.2.2) / h⌋))).card : ℝ) ≤ K / h
  first_coordinate_cap : ∀ i (x y : ℝ),
    (((graph i).filter (fun p : Edge =>
      p.1.1 ∈ Ico x (x + h) ∧ p.2.1 ∈ Ico y (y + h))).card : ℝ) ≤
      K * h ^ 2 * ((graph i).card : ℝ)

/-- The retained-edge planar conclusion, stated independently of its Fourier proof. -/
def PlanarRigidity : Prop :=
  ∀ S : ℝ, 0 < S → ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ ∃ h₀ : ℝ, 0 < h₀ ∧
    ∀ h : ℝ, 0 < h → h < h₀ →
    ∀ d : PlanarGraphData h (h ^ (-η)) S,
    ∃ i : Fin d.size, ∃ G : Finset Edge, G ⊆ d.graph i ∧
      h ^ ε / h ^ 2 ≤ (G.card : ℝ) ∧
      ∃ ℓ c₁ c₂ : ℝ, |ℓ| + |c₁| + |c₂| ≤ h ^ (-ε) ∧
      ∀ p ∈ G, |p.1.2 - ℓ * p.1.1 - c₁| +
        |p.2.2 - ℓ * p.2.1 - c₂| ≤ h ^ (1 - ε)

def trajectoryPosition {α : Type*} (b v : α → ℝ) (p : α × ℝ) : Fin 2 → ℝ :=
  ![p.2, b p.1 + p.2 * v p.1]

noncomputable def positionIndex {α : Type*} (h : ℝ) (b v : α → ℝ)
    (p : α × ℝ) : Fin 2 → ℤ := fun j => ⌊trajectoryPosition b v p j / h⌋

/-- Exactly the incidence hypotheses of the frozen row-fit assertion. -/
structure IncidenceData (S a η N : ℝ) (α : Type) [MeasurableSpace α] where
  prior : Measure α
  active : Measure (α × ℝ)
  intercept : α → ℝ
  velocity : α → ℝ
  evaluation : α → ℝ
  row : α × ℝ → Fin 2 → ℝ
  palette : Measure ℝ
  error : ℝ
  bins : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)
  measurable_intercept : Measurable intercept
  measurable_velocity : Measurable velocity
  measurable_evaluation : Measurable evaluation
  measurable_row : Measurable row
  prior_probability : IsProbabilityMeasure prior
  palette_probability : IsProbabilityMeasure palette
  error_lower : N ^ (-a) ≤ error
  error_upper : error ≤ 1
  trajectory_bound : ∀ l, |intercept l| + |velocity l| ≤ N ^ η
  domination : active ≤ ENNReal.ofReal (N ^ η) • (prior.prod volume)
  time_support : active (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0
  mass_lower : ENNReal.ofReal (N ^ (-η)) ≤ active univ
  palette_cap : ∀ x r : ℝ, N ^ (-a) ≤ r → r ≤ 1 →
    palette (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)
  joint_cap : ∀ (q : Fin 2 → ℤ) (j : ℤ),
    active {p | positionIndex (N ^ (-a)) intercept velocity p = q ∧
      ⌊velocity p.1 / (N ^ (-a))⌋ = j} ≤
      ENNReal.ofReal (N ^ η * (N ^ (-a)) ^ 2) *
        palette (Ico ((j : ℝ) * (N ^ (-a))) (((j : ℝ) + 1) * (N ^ (-a))))
  bins_card : ∀ q, ((bins q).card : ℝ) ≤ N ^ η
  row_constraint : ∀ᵐ p ∂active, (∀ j, |row p j| ≤ N ^ η) ∧
    (fun j => ⌊row p j / error⌋) ∈ bins (positionIndex (N ^ (-a)) intercept velocity p) ∧
    |row p 0 + velocity p.1 * row p 1 - evaluation p.1| ≤ N ^ η * error

/-- Finite graph data with disjoint original incidence witnesses for each edge. -/
structure RowGraphWitness {α : Type} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (z T : α × ℝ → Fin 2 → ℝ)
    (h E K S : ℝ) where
  planar : PlanarGraphData h K S
  v₁ : ℝ
  v₂ : ℝ
  velocity_bound₁ : |v₁| ≤ K
  velocity_bound₂ : |v₂| ≤ K
  velocity_separation : 1 / K ≤ |v₂ - v₁|
  domination : μ ≤ ENNReal.ofReal K • (ν.prod volume)
  witness : Edge → Set (α × ℝ)
  measurable_witness : ∀ e, MeasurableSet (witness e)
  disjoint_witness : Pairwise (fun e f => Disjoint (witness e) (witness f))
  witness_mass : ∀ i e, e ∈ planar.graph i →
    ENNReal.ofReal (h ^ 2 / K) ≤ μ (witness e)
  witness_bounds : ∀ i e, e ∈ planar.graph i → ∀ p ∈ witness e,
    |z p 0| ≤ 1 ∧ |z p 1| ≤ K ∧ (∀ j, |T p j| ≤ K)
  witness_projections : ∀ i e, e ∈ planar.graph i → ∀ p ∈ witness e,
    |z p 1 - v₁ * z p 0 - e.1.1| ≤ K * h ∧
    |(h / E) * (T p 0 + v₁ * T p 1) - e.1.2| ≤ K * h ∧
    |z p 1 - v₂ * z p 0 - e.2.1| ≤ K * h ∧
    |(h / E) * (T p 0 + v₂ * T p 1) - e.2.2| ≤ K * h

/-- The remaining incidence-to-graph reduction, with a fixed requested loss tolerance. -/
def GraphReduction : Prop :=
  ∀ S a θ : ℝ, 0 < S → 0 < a → 0 < θ →
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
    ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α],
    ∀ d : IncidenceData S a η N α,
    Nonempty (RowGraphWitness d.prior d.active
      (trajectoryPosition d.intercept d.velocity) d.row
      (N ^ (-a)) d.error ((N ^ (-a)) ^ (-θ)) (S / 4))

/-- The uniform row-fit conclusion, with the configuration packed into one structure. -/
def UniformRowFit : Prop :=
  ∀ S a ε : ℝ, 0 < S → 0 < a → 0 < ε →
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
    ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α],
    ∀ d : IncidenceData S a η N α,
    ∃ (B : Fin 2 → ℝ) (ℓ : ℝ), |B 0| + |B 1| + |ℓ| ≤ N ^ ε ∧
      ENNReal.ofReal (N ^ (-ε)) ≤ d.active {p |
        |d.row p 0 - B 0 + ℓ * trajectoryPosition d.intercept d.velocity p 1| ≤ N ^ ε * d.error ∧
        |d.row p 1 - B 1 - ℓ * trajectoryPosition d.intercept d.velocity p 0| ≤ N ^ ε * d.error}

end Submission.Obl.k4_affine_skew_row_fit
