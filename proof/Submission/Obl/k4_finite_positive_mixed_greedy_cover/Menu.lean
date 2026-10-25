import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Interface
import Submission.Obl.k4_quadratic_finite_greedy_cover.GainMenu

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

noncomputable section

/-- The fixed geometric menu is finite below the gain ceiling. -/
theorem geometric_menu (gain ρ : ℝ) (hg : 0 < gain) (hρ : 0 < ρ) :
    ∃ M : ℕ, 0 < M ∧ ∀ h : ℝ, gain ≤ h → h ≤ 1 / 8 →
      ∃ e : Fin M, gain ≤ gain * (1 + ρ) ^ (e : ℕ) ∧
        gain * (1 + ρ) ^ (e : ℕ) ≤ h ∧
        h ≤ (1 + ρ) * (gain * (1 + ρ) ^ (e : ℕ)) := by
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt ((1 / 8 : ℝ) / gain) (by linarith : 1 < 1 + ρ)
  refine ⟨M + 1, by omega, ?_⟩
  intro h hgh hh
  obtain ⟨e, he, he'⟩ := exists_nat_pow_near ((one_le_div hg).mpr hgh)
    (by linarith : 1 < 1 + ρ)
  have heM : e ≤ M := by
    by_contra hnot
    have hpow : (1 + ρ) ^ M ≤ (1 + ρ) ^ e :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hrat : h / gain ≤ (1 / 8 : ℝ) / gain := div_le_div_of_nonneg_right hh hg.le
    linarith
  refine ⟨⟨e, by omega⟩, ?_, (by simpa [mul_comm] using (le_div_iff₀ hg).mp he), ?_⟩
  · nlinarith [one_le_pow₀ (by linarith : 1 ≤ 1 + ρ) (n := e)]
  · have hh' := (div_lt_iff₀ hg).mp he'
    rw [pow_succ] at hh'
    nlinarith

/-- The fourfold loss pays for down-rounding the actual gain. -/
theorem rounded_exponents (d ρ h H L e ε : ℝ)
    (hd : 0 ≤ d) (hd' : d ≤ 1) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1 / 4)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hh : h ≤ (1 + ρ) * H) (he : e ≤ ε) (hε : 0 ≤ ε) :
    (d + ρ) * h * L + e ≤ (d + 4 * ρ) * H * L + 4 * ε ∧
    ρ * h * L + e ≤ 4 * ρ * H * L + 4 * ε := by
  have hρsq : ρ * ρ ≤ ρ / 4 := by nlinarith
  have hdρ : d * ρ ≤ ρ := mul_le_of_le_one_left hρ hd'
  have hh1 := mul_le_mul_of_nonneg_left hh (add_nonneg hd hρ)
  have hh2 := mul_le_mul_of_nonneg_left hh hρ
  have ha : (d + ρ) * h ≤ (d + 4 * ρ) * H := by
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ 3 * ρ - d * ρ - ρ * ρ) hH]
  have hb : ρ * h ≤ 4 * ρ * H := by
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ 3 * ρ - ρ * ρ) hH]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right ha hL,
    mul_le_mul_of_nonneg_right hb hL]

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
