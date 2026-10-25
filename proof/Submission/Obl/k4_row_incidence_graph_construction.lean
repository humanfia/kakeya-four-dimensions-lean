import Mathlib
import ChallengeDeps
import Submission.Obl.k4_row_incidence_graph_construction.FrozenPacking
import Submission.Obl.k4_row_incidence_graph_construction.Budget

open Submission.Obl.k4_row_incidence_graph_construction
set_option linter.unusedVariables false

/-!
# `Submission.k4_row_incidence_graph_construction`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_row_incidence_graph_construction`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_row_incidence_graph_construction/`
belong to this obligation.
-/

theorem Submission.k4_row_incidence_graph_construction : ∀ S a θ : ℝ, 0 < S → 0 < a → 0 < θ → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b v H : α → ℝ) (T : α × ℝ → Fin 2 → ℝ) (π : MeasureTheory.Measure ℝ) (E : ℝ) (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)), (fun h : ℝ => (fun K : ℝ => (fun z : α × ℝ → Fin 2 → ℝ => (fun q : α × ℝ → Fin 2 → ℤ => (Measurable b) → (Measurable v) → (Measurable H) → (Measurable T) → (MeasureTheory.IsProbabilityMeasure ν) → (MeasureTheory.IsProbabilityMeasure π) → (h ≤ E) → (E ≤ 1) → (∀ l, |b l| + |v l| ≤ N ^ η) → (μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume)) → (μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) → (ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ) → (∀ x r : ℝ, h ≤ r → r ≤ 1 → π (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) → (∀ (q₀ : Fin 2 → ℤ) (j : ℤ), μ {p | q p = q₀ ∧ ⌊v p.1 / h⌋ = j} ≤ ENNReal.ofReal (N ^ η * h ^ 2) * π (Set.Ico ((j : ℝ) * h) (((j : ℝ) + 1) * h))) → (∀ q₀, ((F q₀).card : ℝ) ≤ N ^ η) → (∀ᵐ p ∂μ, (∀ j, |T p j| ≤ N ^ η) ∧ (fun j => ⌊T p j / E⌋) ∈ F (q p) ∧ |T p 0 + v p.1 * T p 1 - H p.1| ≤ N ^ η * E) → ∃ (m : ℕ) (w κ : Fin m → ℝ) (A B : Finset (ℝ × ℝ)) (G : Fin m → Finset ((ℝ × ℝ) × (ℝ × ℝ))) (u₁ u₂ : ℝ) (W : ((ℝ × ℝ) × (ℝ × ℝ)) → Set (α × ℝ)), (∀ x ∈ A, ∃ a b : ℤ, x = (h * a, h * b)) ∧ (∀ y ∈ B, ∃ a b : ℤ, y = (h * a, h * b)) ∧ (∀ x ∈ A, |x.1| ≤ K ∧ |x.2| ≤ K) ∧ (∀ y ∈ B, |y.1| ≤ K ∧ |y.2| ≤ K) ∧ (1 / (K * h) ≤ (A.card : ℝ)) ∧ ((A.card : ℝ) ≤ K / h) ∧ (1 / (K * h) ≤ (B.card : ℝ)) ∧ ((B.card : ℝ) ≤ K / h) ∧ (∀ i : Fin m, 0 ≤ w i) ∧ ((∑ i : Fin m, w i) = 1) ∧ (∀ i : Fin m, 1 / K ≤ |κ i| ∧ |κ i| ≤ K) ∧ (∀ x r : ℝ, h ≤ r → r ≤ 1 → (∑ i : Fin m, if κ i ∈ Set.Icc x (x + r) then w i else 0) ≤ K * r ^ (S / 4)) ∧ (∀ i : Fin m, G i ⊆ A ×ˢ B) ∧ (∀ i : Fin m, 1 / (K * h ^ 2) ≤ ((G i).card : ℝ)) ∧ (∀ i : Fin m, (((G i).image (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => (⌊(p.1.1 + κ i * p.2.1) / h⌋, ⌊(p.1.2 + κ i * p.2.2) / h⌋))).card : ℝ) ≤ K / h) ∧ (∀ (i : Fin m) (x y : ℝ), (((G i).filter (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => p.1.1 ∈ Set.Ico x (x + h) ∧ p.2.1 ∈ Set.Ico y (y + h))).card : ℝ) ≤ K * h ^ 2 * ((G i).card : ℝ)) ∧ (|u₁| ≤ K) ∧ (|u₂| ≤ K) ∧ (1 / K ≤ |u₂ - u₁|) ∧ (μ ≤ ENNReal.ofReal K • (ν.prod MeasureTheory.volume)) ∧ (∀ e, MeasurableSet (W e)) ∧ (Pairwise (fun e f => Disjoint (W e) (W f))) ∧ (∀ (i : Fin m) e, e ∈ G i → ENNReal.ofReal (h ^ 2 / K) ≤ μ (W e)) ∧ (∀ (i : Fin m) e, e ∈ G i → ∀ p ∈ W e, |z p 0| ≤ 1 ∧ |z p 1| ≤ K ∧ (∀ j, |T p j| ≤ K)) ∧ (∀ (i : Fin m) e, e ∈ G i → ∀ p ∈ W e, |z p 1 - u₁ * z p 0 - e.1.1| ≤ K * h ∧ |(h / E) * (T p 0 + u₁ * T p 1) - e.1.2| ≤ K * h ∧ |z p 1 - u₂ * z p 0 - e.2.1| ≤ K * h ∧ |(h / E) * (T p 0 + u₂ * T p 1) - e.2.2| ≤ K * h)) (fun p j => ⌊z p j / h⌋)) (fun p => ![p.2, b p.1 + p.2 * v p.1])) (h ^ (-θ))) (N ^ (-a)) := by
  intro S a θ hS ha hθ
  obtain ⟨ε, hε, NB, hNB, hbudget⟩ :=
    subpower_parameters (S / 4) a θ (by positivity) ha hθ
  obtain ⟨η, hη, NR, hNR, hreg⟩ :=
    cell_regularization_of_frozen S a ε hS ha hε
  refine ⟨η, hη, max NR NB, hNR.trans (le_max_left _ _), ?_⟩
  intro N hN α inst ν μ b v H T π E F
  dsimp only
  intro hb hv hH hT hν hπ hE hE1 hbv hdom htime hmass hπcap hjoint hbins hrow
  let d : IncidenceData S a η N α := {
    prior := ν
    active := μ
    intercept := b
    velocity := v
    evaluation := H
    row := T
    palette := π
    error := E
    bins := F
    measurable_intercept := hb
    measurable_velocity := hv
    measurable_evaluation := hH
    measurable_row := hT
    prior_probability := hν
    palette_probability := hπ
    error_lower := hE
    error_upper := hE1
    trajectory_bound := hbv
    domination := hdom
    time_support := htime
    mass_lower := hmass
    palette_cap := hπcap
    joint_cap := hjoint
    bins_card := hbins
    row_constraint := hrow
  }
  have hNRN : NR ≤ N := (le_max_left _ _).trans hN
  have hNBN : NB ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNR.trans hNRN
  have hNpos : 0 < N := by linarith
  have hh : 0 < N ^ (-a) := Real.rpow_pos_of_pos hNpos _
  have hh1 : N ^ (-a) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  obtain ⟨r⟩ := hreg N hNRN α d
  obtain ⟨g⟩ := finite_assembly_of_frozen d.prior d.active
    (trajectoryPosition d.intercept d.velocity) d.row
    hh hh1 r.base_lower r.separation_lower r.base_le_separation (by positivity)
    (hbudget N hNBN r.base r.separation r.base_lower r.base_le_separation r.subpower)
    r.finite r.cells r.domination
  exact ⟨g.planar.size, g.planar.weight, g.planar.ratio, g.planar.left, g.planar.right,
    g.planar.graph, g.v₁, g.v₂, g.witness,
    g.planar.left_grid, g.planar.right_grid, g.planar.left_bound, g.planar.right_bound, g.planar.left_card_lower, g.planar.left_card_upper, g.planar.right_card_lower, g.planar.right_card_upper, g.planar.weight_nonneg, g.planar.sum_weight, g.planar.ratio_bound, g.planar.ratio_cap, g.planar.graph_subset, g.planar.graph_card, g.planar.sum_card, g.planar.first_coordinate_cap,
    g.velocity_bound₁, g.velocity_bound₂, g.velocity_separation, g.domination, g.measurable_witness, g.disjoint_witness, g.witness_mass, g.witness_bounds, g.witness_projections⟩
