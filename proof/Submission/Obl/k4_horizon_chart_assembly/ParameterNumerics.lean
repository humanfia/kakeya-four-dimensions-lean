import Mathlib

/-!
Adapted from this LOT tree, o103, session x0354, commit 1552721,
`Submission/Obl/k4_initial_horizon_bound/InitialParameters.lean`.
The plank exponent is chosen before its returned duration exponent. Separate
lower and upper mesh growth exponents are permitted here.
-/

namespace Submission.Obl.k4_horizon_chart_assembly

/-- Choose the plank loss before its returned duration exponent, with separate
fixed polynomial exponents bounding the mesh from below and above. -/
theorem atlas_plank_loss_choice {ε lower upper : ℝ}
    (hε : 0 < ε) (hlower : 0 < lower) (hupper : 0 < upper) :
    ∃ ζ : ℝ, 0 < ζ ∧ upper * ζ ≤ ε / 100 ∧ ∀ η : ℝ, 0 < η →
      ∃ σ : ℝ, 0 < σ ∧ σ ≤ lower * η ∧ σ ≤ ε / 100 ∧
        2 * σ + upper * ζ ≤ ε / 10 := by
  let ζ := ε / (100 * upper)
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have heq : upper * ζ = ε / 100 := by dsimp [ζ]; field_simp
  refine ⟨ζ, hζ, heq.le, ?_⟩
  intro η hη
  let σ := min (lower * η / 2) (ε / 100)
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  have hσ₁ : σ ≤ lower * η / 2 := min_le_left _ _
  have hσ₂ : σ ≤ ε / 100 := min_le_right _ _
  refine ⟨σ, hσ, ?_, hσ₂, ?_⟩
  · have : 0 < lower * η := mul_pos hlower hη
    linarith
  · rw [heq]
    linarith

/-- A polynomial lower mesh bound permits the power duration cut. -/
theorem mesh_duration_power_le {N D A η σ : ℝ} (hN : 1 ≤ N)
    (hmesh : N ^ A ≤ D) (hη : 0 < η) (hσ : σ ≤ A * η) :
    D ^ (-η) ≤ N ^ (-σ) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  calc
    _ ≤ (N ^ A) ^ (-η) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNpos A) hmesh (by linarith)
    _ = N ^ (-(A * η)) := by rw [← Real.rpow_mul hNpos.le]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The duration and typical-density losses fit into the requested slack after
cancelling the physical cell volume. -/
theorem atlas_residual_ratio_le {N D A ζ σ ε : ℝ} (hN : 1 ≤ N)
    (hD : 0 ≤ D) (hupper : D ≤ N ^ A) (hζ : 0 ≤ ζ)
    (hgap : 2 * σ + A * ζ ≤ ε / 2) :
    N ^ σ * D ^ ζ / (N ^ (-σ) * N ^ ε) ≤ N ^ (-ε / 2) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hpow : D ^ ζ ≤ N ^ (A * ζ) := by
    rw [Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow hD hupper hζ
  calc
    _ ≤ N ^ σ * N ^ (A * ζ) / (N ^ (-σ) * N ^ ε) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (by positivity)
    _ = N ^ (2 * σ + A * ζ - ε) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_sub hNpos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end Submission.Obl.k4_horizon_chart_assembly
