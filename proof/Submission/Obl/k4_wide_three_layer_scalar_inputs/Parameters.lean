import Submission.Obl.k4_wide_three_layer_scalar_inputs.Model

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory Filter

/-- The projected exponents are chosen once, before any subpower loss. -/
structure Parameters (d κ U e₀ buffer : ℝ) where
  s₀ : ℝ
  s : ℝ
  u : ℝ
  v : ℝ
  R : ℝ
  M : ℝ
  s₀_pos : 0 < s₀
  s₀_U : buffer * s₀ < U
  s₀_e : buffer * s₀ < e₀
  s₀_s : s₀ < s
  u_pos : 0 < u
  v_pos : 0 < v
  v_u : v < u
  v_margin : v < (1 - d) * u / 4
  su_U : s + u < U
  su_s₀ : s + u < 3 * s₀ / 2
  wide_variation : (10 / (1 - d) + 3) * u < 2 * κ * (s - s₀)
  wide_block : (10 / (1 - d) + 3) * u < κ * s
  R_one : 1 < R
  M_lower : buffer * s₀ < M
  M_U : buffer * M < U
  M_e : buffer * M < e₀

namespace Parameters

variable {d κ U e₀ buffer : ℝ} (p : Parameters d κ U e₀ buffer)

theorem s_pos : 0 < p.s := p.s₀_pos.trans p.s₀_s

theorem u_lt_s₀ : p.u < p.s₀ / 2 := by linarith [p.su_s₀, p.s₀_s]

theorem sv_U : p.s + p.v < U := by linarith [p.v_u, p.su_U]

theorem M_pos (hb : 0 < buffer) : 0 < p.M :=
  (mul_pos hb p.s₀_pos).trans p.M_lower

theorem coefficient_horizon (hb : 100 < buffer) (hκ : κ ≤ 1) :
    4 * κ * p.s₀ < p.M / 25 := by
  have h100 : 100 * p.s₀ < p.M :=
    (mul_lt_mul_of_pos_right hb p.s₀_pos).trans p.M_lower
  have hk : κ * p.s₀ ≤ p.s₀ := by nlinarith [p.s₀_pos]
  linarith

end Parameters

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Unpack the quantified datum while retaining its complete original
measure and reference content at each requested loss. -/
theorem projected_parameters (h : cfg.Projected) {buffer : ℝ} (hb : 100 < buffer) :
    ∃ p : Parameters cfg.d cfg.κ cfg.U cfg.e₀ buffer,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        cfg.ProjectedAt k p.s₀ p.s p.u p.v p.R p.M ε := by
  rcases h buffer hb with ⟨s₀, s, u, v, R, hs₀, hs₀U, hs₀e, hs₀s,
    hu, hv, hvu, hvm, hsuU, hsus, hwv, hwb, hR, M, hM, hMU, hMe, hdata⟩
  exact ⟨⟨s₀, s, u, v, R, M, hs₀, hs₀U, hs₀e, hs₀s, hu, hv,
    hvu, hvm, hsuU, hsus, hwv, hwb, hR, hM, hMU, hMe⟩, hdata⟩

end Data

/-- A buffer chosen from the common-field constant before the projected
scales pays for both its fine normalized mesh and the native depth. -/
theorem field_horizon_budget {C₀ κ M τ : ℝ} (hC : 100 < C₀)
    (hκ : 0 < κ) (hM : 0 < M) (hτ : 0 ≤ τ) (hτM : τ ≤ M) :
    let buffer := 10000 * C₀ * (1 + κ⁻¹)
    let horizon := 100 * C₀ * (10 * M + τ) / κ + 100 * M
    100 < buffer ∧ 0 < horizon ∧ horizon < buffer * M ∧
      C₀ * (10 * M + τ) ≤ κ * horizon / 100 := by
  dsimp only
  have hC0 : 0 < C₀ := by linarith
  have hi : 0 < κ⁻¹ := inv_pos.mpr hκ
  have hCM : 0 < C₀ * M := mul_pos hC0 hM
  have hCM' : M ≤ C₀ * M := by nlinarith
  have hτ' : C₀ * τ ≤ C₀ * M := mul_le_mul_of_nonneg_left hτM hC0.le
  have hkM : κ * M ≤ κ * (C₀ * M) := mul_le_mul_of_nonneg_left hCM' hκ.le
  have hprod : κ * (100 * C₀ * (10 * M + τ) / κ + 100 * M) =
      100 * C₀ * (10 * M + τ) + 100 * κ * M := by field_simp
  have hbprod : κ * (10000 * C₀ * (1 + κ⁻¹) * M) =
      10000 * C₀ * (κ + 1) * M := by field_simp
  refine ⟨by nlinarith, by positivity, ?_, ?_⟩
  · have hh : κ * (100 * C₀ * (10 * M + τ) / κ + 100 * M) <
        κ * (10000 * C₀ * (1 + κ⁻¹) * M) := by
      rw [hprod, hbprod]
      nlinarith
    exact (mul_lt_mul_iff_right₀ hκ).mp hh
  · rw [hprod]
    nlinarith

end Submission.Obl.k4_wide_three_layer_scalar_inputs
