import Submission.Obl.k4_scalar_grid_cartesian_field.DataFacts

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- The angular marginal cap retains the requested compact quantifier without choosing a world. -/
theorem original_angular_cap_compact (data : Data) (hcap : capHyp data)
    (R : ℝ) (hR : 1 < R) : ∀ᶠ k in atTop, ∀ (g : Fin (data.W k)) (r : ℝ),
      R⁻¹ ≤ r → r ≤ R → ∀ c : ℤ, data.π k g (vel data k r c) ≤
        ENNReal.ofReal (data.K k * data.N k ^ (-data.S * r)) := by
  have hRinv : R⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hR.le
  filter_upwards [hcap R hR] with k hk
  exact fun g r hr₀ hr₁ => (hk g 1 1 r hRinv hR.le hRinv hR.le hr₀ hr₁).1

/-- The one fixed original rectangular scale needed for all normalized base ceilings. -/
theorem original_base_rectangle_cap (data : Data) (hs : scaleHyp data) (hcap : capHyp data) :
    ∀ᶠ k in atTop, ∀ (g : Fin (data.W k)) (q : Fin 2 → ℤ) (c : ℤ), data.ρ k g
      {x | (fun e : Fin 2 => (⌊(![x.2, scalarY x.1 x.2] : Fin 2 → ℝ) e /
        data.N k ^ (-(10 + data.κ))⌋ : ℤ)) = q ∧
        (⌊scalarX x.1 x.2 / data.N k ^ (-1 : ℝ)⌋ : ℤ) = c} ≤
      ENNReal.ofReal (data.K k * data.N k ^ (-2 * (10 + data.κ) - data.d)) := by
  have hκ : 0 < data.κ := hs.2.2.2.2.2.1
  have hκone : data.κ ≤ 1 := hs.2.2.2.2.2.2.1
  filter_upwards [hcap 12 (by norm_num)] with k hk
  intro g q c
  have h := (hk g (10 + data.κ) 1 1 (by norm_num; linarith) (by linarith)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.1 q c
  have hz : z data (data.N k) (10 + data.κ) = fun p e =>
      (⌊(![p.2, scalarY p.1 p.2] : Fin 2 → ℝ) e / data.N k ^ (-(10 + data.κ))⌋ : ℤ) := rfl
  rw [hz] at h
  simpa only [x_eq_scalarX, mul_one] using h

end Submission.Obl.k4_scalar_grid_cartesian_field
