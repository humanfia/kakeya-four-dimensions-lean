import Submission.Obl.k4_wide_three_layer_scalar_inputs.ComparisonTarget
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Field.Transport

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory Set Filter

noncomputable section

namespace Field

/-- Choose the field constant before the projected buffer and all its
depths. The mesh exponent has no absolute additive term. -/
theorem commonField_at (h : CommonField) (S : ℝ) (hS : 0 < S) :
    ∃ C₀ : ℝ, 100 < C₀ ∧ ∀ A τ : ℝ, 0 < A → 0 < τ → ∀ ε : ℝ, 0 < ε →
      ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
        ∀ N : ℝ, N₀ ≤ N → FieldAt S C₀ A τ ε η N := h S hS

end Field

/-- Fixed native and field horizons from the buffered projected parameters.
Every exponent scales with `M`, including the deep atlas horizon. -/
theorem native_horizon_choices {d κ U e₀ C₀ : ℝ}
    (hC : 100 < C₀) (hd0 : 0 ≤ d) (hd1 : d < 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (p : Parameters d κ U e₀ (10000 * C₀ * (1 + κ⁻¹))) :
    let τ := (1 - d) * p.u / 2
    let se := 100 * C₀ * (10 * p.M + τ) / κ + 100 * p.M
    0 < τ ∧ 2 * p.v < τ ∧ τ ≤ p.M ∧
      0 < p.M ∧ 0 < 2 * p.M ∧ p.v < 2 * p.M ∧ κ * p.s ≤ 2 * p.M ∧
      p.M < 2 * p.M ∧ p.s + p.v ≤ U ∧ 17 ≤ 17 + 2 * p.s ∧
      p.s < se ∧ se < U ∧ se < e₀ ∧ C₀ * (10 * p.M + τ) ≤ κ * se / 100 := by
  dsimp only
  have hb : 100 < 10000 * C₀ * (1 + κ⁻¹) := by
    have hi : 0 < κ⁻¹ := inv_pos.mpr hκ
    nlinarith
  have hM : 0 < p.M := p.M_pos (by linarith)
  have hMsmall : 100 * p.s₀ < p.M :=
    (mul_lt_mul_of_pos_right hb p.s₀_pos).trans p.M_lower
  have hτ : 0 < (1 - d) * p.u / 2 :=
    div_pos (mul_pos (sub_pos.mpr hd1) p.u_pos) (by norm_num)
  have hτM : (1 - d) * p.u / 2 ≤ p.M := by
    have hu := p.u_lt_s₀
    nlinarith [mul_nonneg hd0 p.u_pos.le]
  have hh := field_horizon_budget hC hκ hM hτ.le hτM
  dsimp only at hh
  have hsM : p.s < p.M := by linarith [p.su_s₀, p.u_pos]
  have hκs : κ * p.s ≤ p.s := mul_le_of_le_one_left p.s_pos.le hκ1
  have hseM : 100 * p.M < 100 * C₀ * (10 * p.M + (1 - d) * p.u / 2) / κ + 100 * p.M := by
    have hC0 : 0 < C₀ := by linarith
    have := div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 100) hC0)
      (by positivity : 0 < 10 * p.M + (1 - d) * p.u / 2)) hκ
    linarith
  refine ⟨hτ, by linarith [p.v_margin], hτM, hM, by positivity, ?_, ?_, by linarith,
    p.sv_U.le, by linarith [p.s_pos], ?_, hh.2.2.1.trans p.M_U, hh.2.2.1.trans p.M_e,
    hh.2.2.2⟩
  · linarith [p.v_u, p.u_lt_s₀]
  · linarith
  · linarith

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The same native witness supplies every larger loss. -/
theorem extractionAt_mono {k : ℕ} {θ₁ θ₂ s v m J : ℝ} (hN : 1 ≤ cfg.N k)
    (hθ : θ₁ ≤ θ₂) (h : cfg.ExtractionAt k θ₁ s v m J) :
    cfg.ExtractionAt k θ₂ s v m J := by
  dsimp only [ExtractionAt] at h ⊢
  obtain ⟨i, lam, Bs, L, C, hBs, hsub, hlam, hsupp, hmass, hL, hC, hgeom, Fs, hcard, hFs⟩ := h
  have hp := Real.rpow_le_rpow_of_exponent_le hN hθ
  have hn := Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hθ)
  refine ⟨i, lam, Bs, L, C, hBs, hsub, hlam, hsupp, ?_, hL, fun e => (hC e).trans hp,
    ?_, Fs, ?_, hFs⟩
  · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hn) le_rfl).trans hmass
  · intro l hl t ht
    obtain ⟨h1, h2, h3⟩ := hgeom l hl t ht
    exact ⟨h1.trans hp, h2.trans hp, h3.trans hp⟩
  · exact hcard.trans (mul_le_mul_of_nonneg_right hp
      (Real.rpow_nonneg (Real.rpow_nonneg (zero_le_one.trans hN) _) _))

/-- It suffices to run the construction below one fixed positive loss. -/
theorem extractionAt_all_losses {s v m J θ₀ : ℝ} (hN : ∀ k, 1 ≤ cfg.N k) (hθ₀ : 0 < θ₀)
    (h : ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∀ᶠ k in atTop, cfg.ExtractionAt k θ s v m J) :
    ∀ θ : ℝ, 0 < θ → ∀ᶠ k in atTop, cfg.ExtractionAt k θ s v m J := by
  intro θ hθ
  filter_upwards [h (min θ θ₀) (lt_min hθ hθ₀) (min_le_right _ _)] with k hk
  exact extractionAt_mono (hN k) (min_le_left _ _) hk

end Data

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
