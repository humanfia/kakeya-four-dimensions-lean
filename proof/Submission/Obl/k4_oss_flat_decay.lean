import Submission.Obl.k4_oss_flat_decay.Flatness

theorem Submission.k4_oss_flat_decay : ∀ s : ℝ, 0 < s → s ≤ 1 → ∃ γ ε τ δ₀ : ℝ, 0 < γ ∧ 0 < ε ∧ 0 < τ ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ α β : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → MeasureTheory.IsProbabilityMeasure β → α (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → β (Set.Icc (1 : ℝ) 2)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → β (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) → (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ≤ ENNReal.ofReal (δ ^ (1 - γ)) → ∀ ζ : ℝ, δ⁻¹ ≤ |ζ| → |ζ| ≤ 2 * δ⁻¹ → ‖MeasureTheory.integral (α.prod β) (fun p : ℝ × ℝ => Complex.exp (((-2 * Real.pi * ζ * (p.1 * p.2) : ℝ) : ℂ) * Complex.I))‖ ≤ δ ^ τ := by
  intro s hs hs1
  obtain ⟨γ, ε, τ, δ₀, hγ, hγ1, hε, hτ, hδ₀, h⟩ :=
    Submission.Obl.k4_oss_flat_decay.fourier_decay_of_collision_flatness s hs hs1
  refine ⟨γ, ε, τ, δ₀, hγ, hε, hτ, hδ₀, ?_⟩
  intro δ hδ hδsmall α β hα hβ hαsupp hβsupp hcap hflat ζ hζlo hζhi
  simpa only [mul_assoc] using
    h δ hδ hδsmall α β hα hβ hαsupp hβsupp hflat hcap ζ hζlo hζhi
