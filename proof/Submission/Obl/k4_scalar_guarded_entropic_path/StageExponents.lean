import Mathlib

/-! Width, current-floor and density losses are fixed after the common
power allowance. Every one remains a positive original-scale exponent. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

noncomputable section

structure PreparationExponents (scale δ v S₀ η : ℝ) where
  u : ℝ
  ε : ℝ
  γ : ℝ
  τ : ℝ
  u_pos : 0 < u
  ε_pos : 0 < ε
  γ_pos : 0 < γ
  τ_pos : 0 < τ
  u_angular : u ≤ η / 2
  ε_width : ε ≤ S₀ * u / 4
  ε_small : ε ≤ v / 100
  width_gap : ε + u < v
  γ_small : γ ≤ v / 100
  γ_budget : γ ≤ scale * δ / 10000
  τ_budget : τ ≤ scale * δ / 100000
  τ_scale : τ ≤ scale / 100000

/-- The positive width-fitting tolerance already witnesses positivity
of the original angular exponent; later reference inputs need no new
assumption about it. -/
theorem PreparationExponents.S_pos {scale δ v S₀ η : ℝ}
    (pe : PreparationExponents scale δ v S₀ η) : 0 < S₀ := by
  by_contra! hS
  have hp : S₀ * pe.u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hS pe.u_pos.le
  linarith only [hp, pe.ε_width, pe.ε_pos]

theorem nonempty_preparationExponents {scale δ v S₀ η : ℝ}
    (hscale : 0 < scale) (hδ : 0 < δ) (hv : 0 < v) (hS : 0 < S₀) (hη : 0 < η) :
    Nonempty (PreparationExponents scale δ v S₀ η) := by
  let u := min (v / 100) (η / 100)
  let ε := min (v / 100) (S₀ * u / 8)
  let γ := min (v / 100) (scale * δ / 10000)
  let τ := min (scale * δ / 100000) (scale / 100000)
  have hu : 0 < u := lt_min (by positivity) (by positivity)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hγ : 0 < γ := lt_min (by positivity) (by positivity)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have huη : u ≤ η / 2 := (min_le_right _ _).trans (by linarith)
  have hεwidth : ε ≤ S₀ * u / 4 :=
    (min_le_right _ _).trans (by nlinarith only [hS, hu])
  have hgap : ε + u < v := by
    have hεv : ε ≤ v / 100 := min_le_left _ _
    have huv : u ≤ v / 100 := min_le_left _ _
    linarith
  exact ⟨⟨u, ε, γ, τ, hu, hε, hγ, hτ, huη, hεwidth, min_le_left _ _, hgap,
    min_le_left _ _, min_le_right _ _, min_le_left _ _, min_le_right _ _⟩⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path
