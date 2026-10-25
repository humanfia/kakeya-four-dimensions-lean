import Submission.Obl.k4_wide_three_layer_scalar_inputs.Parameters

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

noncomputable section

/-- The fixed projected buffer pays every native geometric horizon, so
later loss choices do not move the output scales. -/
theorem native_scale_margins {d κ U e₀ C₀ σ ε : ℝ}
    (hC : 100 < C₀) (hd : 0 ≤ d) (hd1 : d < 1) (hκ : 0 < κ)
    (p : Parameters d κ U e₀ (10000 * C₀ * (1 + κ⁻¹)))
    (hσ : 0 < σ) (hσs : σ ≤ p.s / 100) (hσu : σ ≤ p.u / 100)
    (_hσM : σ ≤ p.M / 100) (hε : ε ≤ (1 - d) * p.u / 200) :
    let τ := (1 - d) * p.u / 2
    let B := C₀ * (10 * p.M + τ)
    let se := 100 * B / κ + 100 * p.M
    0 < p.M ∧ p.s + p.u < p.M / 10 ∧ 10 * p.M ≤ B ∧
      0 < B ∧ p.M ≤ B ∧ 2 * p.u ≤ B ∧
      0 ≤ p.s - 2 * σ ∧
      σ + τ ≤ B ∧ 2 * σ + p.s + τ ≤ p.M ∧ σ + τ ≤ p.M ∧
      σ + p.v ≤ B ∧ 5 * σ + p.v < 2 * p.M ∧
      7 * σ + 2 * p.s - κ * se < -B ∧
      ε + 8 * σ + 2 * p.s - κ * se < -p.v := by
  dsimp only
  have hb : 100 < 10000 * C₀ * (1 + κ⁻¹) := by
    have hi : 0 < κ⁻¹ := inv_pos.mpr hκ
    nlinarith
  have hM : 0 < p.M := p.M_pos (by linarith)
  have hMsmall : 100 * p.s₀ < p.M :=
    (mul_lt_mul_of_pos_right hb p.s₀_pos).trans p.M_lower
  have hsu : p.s + p.u < p.M / 10 := by linarith [p.su_s₀, p.s₀_pos]
  have hτ : 0 < (1 - d) * p.u / 2 := div_pos (mul_pos (sub_pos.mpr hd1) p.u_pos) (by norm_num)
  have hτu : (1 - d) * p.u / 2 ≤ p.u / 2 := by
    nlinarith [mul_nonneg hd p.u_pos.le]
  have hB : 10 * p.M ≤ C₀ * (10 * p.M + (1 - d) * p.u / 2) := by
    nlinarith
  have hBpos : 0 < C₀ * (10 * p.M + (1 - d) * p.u / 2) := by positivity
  have hse : κ * (100 * (C₀ * (10 * p.M + (1 - d) * p.u / 2)) / κ + 100 * p.M) =
      100 * (C₀ * (10 * p.M + (1 - d) * p.u / 2)) + 100 * κ * p.M := by
    field_simp
  have hκM : 0 < κ * p.M := mul_pos hκ hM
  refine ⟨hM, hsu, hB, hBpos, by linarith, by linarith [p.s_pos],
    by linarith [p.s_pos], by linarith, by linarith, by linarith [p.s_pos],
    by linarith [p.v_u], by linarith [p.v_u], ?_, ?_⟩
  · rw [hse]
    linarith [p.u_pos, p.s_pos]
  · rw [hse]
    linarith [p.v_u, p.u_pos, p.s_pos]

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
