import Submission.Obl.k4_finite_row_graph_assembly.Interfaces

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/Unpack.lean.

namespace Submission.Obl.k4_finite_row_graph_assembly

theorem unpack_witness {α : Type} [MeasurableSpace α]
    {ν : MeasureTheory.Measure α} {μ : MeasureTheory.Measure (α × ℝ)}
    {z T : α × ℝ → Fin 2 → ℝ} {h E L s : ℝ}
    (d : RowGraphWitness ν μ z T h E L s) :
    ∃ (m : ℕ) (w κ : Fin m → ℝ) (A B : Finset (ℝ × ℝ)) (G : Fin m → Finset ((ℝ × ℝ) × (ℝ × ℝ))) (u₁ u₂ : ℝ) (W : ((ℝ × ℝ) × (ℝ × ℝ)) → Set (α × ℝ)), (∀ x ∈ A, ∃ a b : ℤ, x = (h * a, h * b)) ∧ (∀ y ∈ B, ∃ a b : ℤ, y = (h * a, h * b)) ∧ (∀ x ∈ A, |x.1| ≤ L ∧ |x.2| ≤ L) ∧ (∀ y ∈ B, |y.1| ≤ L ∧ |y.2| ≤ L) ∧ (1 / (L * h) ≤ (A.card : ℝ)) ∧ ((A.card : ℝ) ≤ L / h) ∧ (1 / (L * h) ≤ (B.card : ℝ)) ∧ ((B.card : ℝ) ≤ L / h) ∧ (∀ i : Fin m, 0 ≤ w i) ∧ ((∑ i : Fin m, w i) = 1) ∧ (∀ i : Fin m, 1 / L ≤ |κ i| ∧ |κ i| ≤ L) ∧ (∀ x r : ℝ, h ≤ r → r ≤ 1 → (∑ i : Fin m, if κ i ∈ Set.Icc x (x + r) then w i else 0) ≤ L * r ^ (s)) ∧ (∀ i : Fin m, G i ⊆ A ×ˢ B) ∧ (∀ i : Fin m, 1 / (L * h ^ 2) ≤ ((G i).card : ℝ)) ∧ (∀ i : Fin m, (((G i).image (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => (⌊(p.1.1 + κ i * p.2.1) / h⌋, ⌊(p.1.2 + κ i * p.2.2) / h⌋))).card : ℝ) ≤ L / h) ∧ (∀ (i : Fin m) (x y : ℝ), (((G i).filter (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => p.1.1 ∈ Set.Ico x (x + h) ∧ p.2.1 ∈ Set.Ico y (y + h))).card : ℝ) ≤ L * h ^ 2 * ((G i).card : ℝ)) ∧ (|u₁| ≤ L) ∧ (|u₂| ≤ L) ∧ (1 / L ≤ |u₂ - u₁|) ∧ (μ ≤ ENNReal.ofReal L • (ν.prod MeasureTheory.volume)) ∧ (∀ e, MeasurableSet (W e)) ∧ (Pairwise (fun e f => Disjoint (W e) (W f))) ∧ (∀ (i : Fin m) e, e ∈ G i → ENNReal.ofReal (h ^ 2 / L) ≤ μ (W e)) ∧ (∀ (i : Fin m) e, e ∈ G i → ∀ p ∈ W e, |z p 0| ≤ 1 ∧ |z p 1| ≤ L ∧ (∀ j, |T p j| ≤ L)) ∧ (∀ (i : Fin m) e, e ∈ G i → ∀ p ∈ W e, |z p 1 - u₁ * z p 0 - e.1.1| ≤ L * h ∧ |(h / E) * (T p 0 + u₁ * T p 1) - e.1.2| ≤ L * h ∧ |z p 1 - u₂ * z p 0 - e.2.1| ≤ L * h ∧ |(h / E) * (T p 0 + u₂ * T p 1) - e.2.2| ≤ L * h) := by
  refine ⟨d.planar.size, d.planar.weight, d.planar.ratio, d.planar.left,
    d.planar.right, d.planar.graph, d.v₁, d.v₂, d.witness,
    d.planar.left_grid, d.planar.right_grid, d.planar.left_bound, d.planar.right_bound,
    d.planar.left_card_lower, d.planar.left_card_upper, d.planar.right_card_lower,
    d.planar.right_card_upper, d.planar.weight_nonneg, d.planar.sum_weight,
    d.planar.ratio_bound, d.planar.ratio_cap, d.planar.graph_subset,
    d.planar.graph_card, d.planar.sum_card, d.planar.first_coordinate_cap,
    d.velocity_bound₁, d.velocity_bound₂, d.velocity_separation, d.domination,
    d.measurable_witness, d.disjoint_witness, d.witness_mass, d.witness_bounds,
    d.witness_projections⟩

end Submission.Obl.k4_finite_row_graph_assembly
