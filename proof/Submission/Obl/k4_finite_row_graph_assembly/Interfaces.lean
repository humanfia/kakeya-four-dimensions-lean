import Mathlib

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/Interfaces.lean.

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_finite_row_graph_assembly

-- Adapted from this LOT tree, o063, session x0213, Interfaces.lean (e15ca2d).

abbrev RealEdge := (ℝ × ℝ) × (ℝ × ℝ)

/-- The finite planar data in Assumption 7.2, with one explicit loss factor. -/
structure PlanarGraphData (h K S : ℝ) where
  size : ℕ
  weight : Fin size → ℝ
  ratio : Fin size → ℝ
  left : Finset (ℝ × ℝ)
  right : Finset (ℝ × ℝ)
  graph : Fin size → Finset RealEdge
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
    (((graph i).image (fun p : RealEdge =>
      (⌊(p.1.1 + ratio i * p.2.1) / h⌋,
        ⌊(p.1.2 + ratio i * p.2.2) / h⌋))).card : ℝ) ≤ K / h
  first_coordinate_cap : ∀ i (x y : ℝ),
    (((graph i).filter (fun p : RealEdge =>
      p.1.1 ∈ Ico x (x + h) ∧ p.2.1 ∈ Ico y (y + h))).card : ℝ) ≤
      K * h ^ 2 * ((graph i).card : ℝ)

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
  witness : RealEdge → Set (α × ℝ)
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


end Submission.Obl.k4_finite_row_graph_assembly
