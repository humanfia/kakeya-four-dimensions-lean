import Submission.Obl.k4_quadratic_candidate_atlas_conversion.Interface

namespace Submission.Obl.k4_quadratic_candidate_atlas_conversion

/-- The width certificate already has the original observation lists. A smaller
retained gain only weakens its determinant bound and terminal margin. -/
theorem width_improvementAt
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (κ₁ gain Δ : ℝ) (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ)
    (Mi Di : ℕ) (τ : ℝ)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hgain : 0 ≤ gain) (hΔ : Δ ≤ gain)
    (hw : width Nk L W ω ν E B m r T nw gain Mi Di τ) :
    ImprovementAt Nk L W ω ν E B κ₁ Δ m r T nw Mi Di τ := by
  rcases hw with ⟨i, hi, hroom, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    hcount, hdisj, hlist, hchart, hmass⟩
  refine ⟨r i, T i, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    ?_, ?_, hcount, hdisj, hlist, ?_, hmass⟩
  · have hg : Δ * L ≤ 2 * gain * L :=
      mul_le_mul_of_nonneg_right (by linarith) hL
    linarith
  · refine Or.inr ⟨i, hi, Or.inr ⟨rfl, rfl, ?_⟩⟩
    intro b
    exact (hchart b).2.trans (Real.rpow_le_rpow_of_exponent_le hN
      (by nlinarith [mul_le_mul_of_nonneg_right hΔ hL]))
  · exact fun b => (hchart b).1

end Submission.Obl.k4_quadratic_candidate_atlas_conversion
