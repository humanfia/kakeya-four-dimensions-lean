import Mathlib

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

noncomputable section

/-- The field's output loss is chosen before invoking its input loss. -/
theorem native_field_loss_choice {θ τ v : ℝ} (hθ : 0 < θ) (hvτ : v < τ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ θ / 100 ∧ ε ≤ (τ - v) / 100 ∧ ε + v ≤ τ := by
  refine ⟨min (θ / 100) ((τ - v) / 100), lt_min (by positivity) (by positivity),
    min_le_left _ _, min_le_right _ _, ?_⟩
  have hh := min_le_right (θ / 100) ((τ - v) / 100)
  linarith

/-- A single comparison subpower fits all mass, coefficient, width and
residual table margins after the field supplies its positive input loss. -/
theorem native_subpower_choices {η β s u M θ ε : ℝ}
    (hη : 0 < η) (hβ : 0 < β) (hs : 0 < s) (hu : 0 < u) (hM : 0 < M)
    (hθ : 0 < θ) (hεθ : ε ≤ θ / 100) :
    ∃ ζ σ : ℝ, 0 < ζ ∧ 0 < σ ∧
      ζ ≤ η / 100 ∧ ζ ≤ β / 100 ∧ σ ≤ ζ / 100 ∧
      σ ≤ s / 100 ∧ σ ≤ u / 100 ∧ σ ≤ M / 100 ∧ σ ≤ θ / 1000 ∧ σ ≤ 1 ∧
      σ < ζ ∧ σ + ζ < η ∧ 6 * σ ≤ η ∧
      10 * σ + ζ < β ∧ 15 * σ + 2 * ε < θ := by
  let ζ := min (η / 100) (β / 100)
  let σ := min (ζ / 100) (min (s / 100) (min (u / 100) (min (M / 100) (min (θ / 1000) 1))))
  have hζ : 0 < ζ := lt_min (by positivity) (by positivity)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hζη : ζ ≤ η / 100 := min_le_left _ _
  have hζβ : ζ ≤ β / 100 := min_le_right _ _
  have hσζ : σ ≤ ζ / 100 := min_le_left _ _
  have hrest : σ ≤ min (s / 100) (min (u / 100) (min (M / 100) (min (θ / 1000) 1))) := min_le_right _ _
  have hσs : σ ≤ s / 100 := hrest.trans (min_le_left _ _)
  have hrest₂ := hrest.trans (min_le_right _ _)
  have hσu : σ ≤ u / 100 := hrest₂.trans (min_le_left _ _)
  have hrest₃ := hrest₂.trans (min_le_right _ _)
  have hσM : σ ≤ M / 100 := hrest₃.trans (min_le_left _ _)
  have hrest₄ := hrest₃.trans (min_le_right _ _)
  have hσθ : σ ≤ θ / 1000 := hrest₄.trans (min_le_left _ _)
  have hσ1 : σ ≤ 1 := hrest₄.trans (min_le_right _ _)
  refine ⟨ζ, σ, hζ, hσ, hζη, hζβ, hσζ, hσs, hσu, hσM, hσθ, hσ1,
    by linarith, by linarith, by linarith, by linarith, by linarith⟩

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
