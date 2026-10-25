import Submission.Obl.k4_initial_horizon_bound.BoundedPacking
import Submission.Obl.k4_initial_horizon_bound.GreedyIndices

namespace Submission.Obl.k4_initial_horizon_bound

/-- Expanded Mathlib-only finite-index form of the per-group greedy core. -/
theorem frozen_mesh_greedy_cover :
    ∀ ε : ℝ, 0 < ε → ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ D : ℕ, 2 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (ν : MeasureTheory.Measure α)
      [MeasureTheory.IsFiniteMeasure ν]
      (b u : α → EuclideanSpace ℝ (Fin 2)),
    Measurable b → Measurable u → ∀ U : Set α, MeasurableSet U →
    (∀ x ∈ U, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
    ((fun fit : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) →
        EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ → ℝ → α → Prop =>
      ∀ E Gd : Set (α × ℝ), MeasurableSet E → MeasurableSet Gd →
        E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
      ∀ τ₀ s : ℝ, 0 < τ₀ → (D : ℝ) ^ (-η) ≤ s →
      ∀ F : Finset (ℤ × (Fin 2 → ℤ)),
      (∀ p ∈ E ∩ Gd, p.1 ∈ U →
        (⌊p.2 * (D : ℝ)⌋, fun k : Fin 2 => ⌊(D : ℝ) * (b p.1 + p.2 • u p.1) k⌋) ∈ F) →
      ∃ (m : ℕ) (c w e₁ e₂ : Fin m → EuclideanSpace ℝ (Fin 2)) (a β : Fin m → ℝ),
        (∀ i, ‖e₁ i‖ = 1 ∧ ‖e₂ i‖ = 1 ∧ inner ℝ (e₁ i) (e₂ i) = 0 ∧
          2 / (D : ℝ) ≤ a i ∧ a i ≤ β i ∧ β i ≤ 2) ∧
        (∀ i, ENNReal.ofReal (τ₀ * a i * β i) ≤ (ν.prod MeasureTheory.volume)
          (E ∩ ({x | x ∈ U ∧ fit (c i) (w i) (e₁ i) (e₂ i) (a i) (β i) x ∧
            ∀ j : Fin m, j < i → ¬ fit (c j) (w j) (e₁ j) (e₂ j) (a j) (β j) x} ×ˢ Set.univ))) ∧
        (ν.prod MeasureTheory.volume) (E ∩
          ({x | x ∈ U ∧ ∀ i, ¬ fit (c i) (w i) (e₁ i) (e₂ i) (a i) (β i) x} ×ˢ Set.univ)) ≤
          (ν.prod MeasureTheory.volume) (E ∩ Gdᶜ ∩
            ({x | x ∈ U ∧ ∀ i, ¬ fit (c i) (w i) (e₁ i) (e₂ i) (a i) (β i) x} ×ˢ Set.univ)) +
          ENNReal.ofReal s * ν {x | x ∈ U ∧ ∀ i, ¬ fit (c i) (w i) (e₁ i) (e₂ i) (a i) (β i) x} +
          ENNReal.ofReal (C * τ₀ * (D : ℝ) ^ ε / (s * (D : ℝ) ^ 3) * (F.card : ℝ)))
      (fun c w e₁ e₂ a β x => ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |inner ℝ (b x + t • u x - c - t • w) e₁| ≤ a ∧
        |inner ℝ (b x + t • u x - c - t • w) e₂| ≤ β)) := by
  intro ε hε
  obtain ⟨η, C, hη, hC, H⟩ := mesh_greedy_plank_cover ε hε
  refine ⟨η, C, hη, hC, ?_⟩
  intro D hD α _ ν _ b u hb hu U hU hbu E Gd hE hGd hunit τ₀ s hτ₀ hlong F hF
  obtain ⟨ps, hwidths, hps, hres⟩ := H D hD α ν b u hb hu U hU hbu E Gd hE hGd hunit
    τ₀ s hτ₀ hlong F hF
  let p : Fin ps.length → PlanarPlank := ps.get
  refine ⟨ps.length, (fun i => (p i).center), (fun i => (p i).speed),
    (fun i => (p i).axis₁), (fun i => (p i).axis₂), (fun i => (p i).thin),
    (fun i => (p i).wide), ?_, ?_, ?_⟩
  · intro i
    have hi : p i ∈ ps := List.get_mem _ _
    exact ⟨(p i).unit₁, (p i).unit₂, (p i).orthogonal, (hwidths _ hi).1,
      (p i).widths_le, (hwidths _ hi).2⟩
  · intro i
    have h := greedyPieces_incidence_floor ν hb hu hU hE hunit hps
      (ps.get i, priorityPiece (fun p => p.lines b u) U ps i)
      (priorityPiece_mem_greedyPieces (fun p => p.lines b u) U ps i)
    simpa only [p, priorityPiece, PlanarPlank.lines, PlanarPlank.area,
      Submission.Lib.K4ContinuousPlanks.InFullTracePlank, Set.mem_ofPred_eq, mul_assoc] using h
  · simpa only [greedyResidual_indices, PlanarPlank.lines,
      Submission.Lib.K4ContinuousPlanks.InFullTracePlank, Set.mem_ofPred_eq, p] using hres

end Submission.Obl.k4_initial_horizon_bound
