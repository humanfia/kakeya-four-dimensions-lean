import Submission.Obl.k4_affine_skew_row_fit.Interfaces

namespace Submission.Obl.k4_affine_skew_row_fit

/-- Unpack the configuration to recover exactly the frozen row-fit conclusion. -/
theorem expanded_of_uniform (huniform : UniformRowFit) : (∀ S a ε : ℝ, 0 < S → 0 < a → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b v H : α → ℝ) (T : α × ℝ → Fin 2 → ℝ) (π : MeasureTheory.Measure ℝ) (E : ℝ) (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)), (fun ξ : ℝ => (fun z : α × ℝ → Fin 2 → ℝ => (fun q : α × ℝ → Fin 2 → ℤ => Measurable b → Measurable v → Measurable H → Measurable T → MeasureTheory.IsProbabilityMeasure ν → MeasureTheory.IsProbabilityMeasure π → ξ ≤ E → E ≤ 1 → (∀ l, |b l| + |v l| ≤ N ^ η) → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ x r : ℝ, ξ ≤ r → r ≤ 1 → π (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) → (∀ (p₀ : Fin 2 → ℤ) (j : ℤ), μ {p | q p = p₀ ∧ ⌊v p.1 / ξ⌋ = j} ≤ ENNReal.ofReal (N ^ η * ξ ^ 2) * π (Set.Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ))) → (∀ p₀, ((F p₀).card : ℝ) ≤ N ^ η) → (∀ᵐ p ∂μ, (∀ j, |T p j| ≤ N ^ η) ∧ (fun j => ⌊T p j / E⌋) ∈ F (q p) ∧ |T p 0 + v p.1 * T p 1 - H p.1| ≤ N ^ η * E) → ∃ (B : Fin 2 → ℝ) (ℓ : ℝ), |B 0| + |B 1| + |ℓ| ≤ N ^ ε ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | |T p 0 - B 0 + ℓ * z p 1| ≤ N ^ ε * E ∧ |T p 1 - B 1 - ℓ * z p 0| ≤ N ^ ε * E}) (fun p j => ⌊z p j / ξ⌋)) (fun p => ![p.2, b p.1 + p.2 * v p.1])) (N ^ (-a))) := by
  intro S a ε hS ha hε
  obtain ⟨η, hη, N₀, hN₀, h⟩ := huniform S a ε hS ha hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α inst ν μ b v H T π E F hb hv hH hT hν hπ hElo hEhi
    hbound hdom hsupp hmass hπcap hjoint hF hrow
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
    error_lower := hElo
    error_upper := hEhi
    trajectory_bound := hbound
    domination := hdom
    time_support := hsupp
    mass_lower := hmass
    palette_cap := hπcap
    joint_cap := hjoint
    bins_card := hF
    row_constraint := hrow }
  exact h N hN α d

end Submission.Obl.k4_affine_skew_row_fit
