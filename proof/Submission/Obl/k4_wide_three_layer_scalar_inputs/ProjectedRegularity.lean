import Submission.Obl.k4_wide_three_layer_scalar_inputs.Model
import Submission.Obl.k4_wide_three_layer_scalar_inputs.StripCoefficients

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory Filter MvPolynomial

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The same retained law and all three original layers admit the sharp
physical coefficient budget. Every other bound only enlarges its loss. -/
theorem projectedAt_rebound {k : ℕ} {s₀ s u v R M ε : ℝ}
    (hN : 1 ≤ cfg.N k) (hκ : 0 ≤ cfg.κ) (hs₀ : 0 ≤ s₀) (hε : 0 ≤ ε)
    (hnum : 2160 * cfg.N k ^ (4 * cfg.κ * s₀ + 3 * ε) ≤
      cfg.N k ^ (4 * cfg.κ * s₀ + 6 * ε))
    (hData : cfg.ProjectedAt k s₀ s u v R M ε) :
    cfg.ProjectedAt k s₀ s u v (4 * cfg.κ * s₀ + 6 * ε) M (6 * ε) := by
  have hNp : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hp : cfg.N k ^ ε ≤ cfg.N k ^ (6 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hn : cfg.N k ^ (-(6 * ε)) ≤ cfg.N k ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  dsimp only [ProjectedAt] at hData ⊢
  rcases hData with ⟨ρs, np, Cp, qp, Gp, hρ, hmass, hcover, hmeas, hdisj,
    hlayers, hsum, hagree⟩
  refine ⟨ρs, np, Cp, qp, Gp, hρ, (ENNReal.ofReal_le_ofReal hn).trans hmass,
    hcover, hmeas, hdisj, ?_, ?_, ?_⟩
  · intro h i
    rcases hlayers h i with ⟨hbin, hcorner, hdeg, hcoeff, hnorm, hfit, hfloor⟩
    refine ⟨?_, hcorner.trans hp, hdeg, ?_, ?_, ?_, ?_⟩
    · intro l hl
      rcases hbin l hl with ⟨hb0, hb1, hb2, hb⟩
      exact ⟨hb0, hb1, hb2, fun e => (hb e).trans hp⟩
    · intro e
      have hcenter : |(qp h i 2 : ℝ) * cfg.N k ^ (-2 * cfg.κ * s₀)| +
          |-((qp h i 1 : ℝ) * cfg.N k ^ (-M))| ≤ cfg.N k ^ ε := by
        rw [abs_neg]
        linarith [abs_nonneg ((qp h i 0 : ℝ) * cfg.N k ^ (-M))]
      have hnorm' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
          |eval ![t, (qp h i 2 : ℝ) * cfg.N k ^ (-2 * cfg.κ * s₀) +
            t * (-((qp h i 1 : ℝ) * cfg.N k ^ (-M))) +
            cfg.N k ^ (-(2 * cfg.κ * s₀)) * w] (Gp h i)| ≤ cfg.N k ^ ε := by
        intro t ht w hw
        convert hnorm t ht w hw using 1 <;> congr 2 <;> ring
      have hbd := moving_strip_coefficients_power hN
        (show 0 ≤ 2 * cfg.κ * s₀ by positivity) hε (Gp h i) hdeg hcenter hnorm' e
      have heq : 2 * (2 * cfg.κ * s₀) + 3 * ε = 4 * cfg.κ * s₀ + 3 * ε := by ring
      rw [heq] at hbd
      exact hbd.trans hnum
    · intro t ht w hw
      exact (hnorm t ht w hw).trans hp
    · intro l hl t ht
      exact ⟨(hfit l hl t ht).1.trans (mul_le_mul_of_nonneg_right hp (by positivity)),
        (hfit l hl t ht).2.trans (mul_le_mul_of_nonneg_right hp (by positivity))⟩
    · apply le_trans _ hfloor
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hp
  · intro h
    exact (hsum h).trans (ENNReal.ofReal_le_ofReal hp)
  · filter_upwards [hagree] with p hp'
    intro h hh i₀ ih hi₀ hih t ht w hw
    exact (hp' h hh i₀ ih hi₀ hih t ht w hw).trans
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by positivity))

/-- The sharp physical budget is available at every requested loss, with
all geometric exponents fixed beforehand. -/
theorem eventually_projectedAt_rebound (h : cfg.Valid) {s₀ s u v R M : ℝ}
    (hs₀ : 0 ≤ s₀)
    (hData : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      cfg.ProjectedAt k s₀ s u v R M ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      cfg.ProjectedAt k s₀ s u v (4 * cfg.κ * s₀ + ε) M ε := by
  intro ε hε
  have hnum := h.scale_limit.eventually
    (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 2160
      (show 4 * cfg.κ * s₀ + 3 * (ε / 6) <
        4 * cfg.κ * s₀ + 6 * (ε / 6) by linarith))
  filter_upwards [hData (ε / 6) (by positivity), hnum] with k hk hn
  have hh := projectedAt_rebound (show 1 ≤ cfg.N k by linarith [h.scale k])
    h.rate_pos.le hs₀ (show 0 ≤ ε / 6 by positivity) hn hk
  convert hh using 1 <;> ring


end Data

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
