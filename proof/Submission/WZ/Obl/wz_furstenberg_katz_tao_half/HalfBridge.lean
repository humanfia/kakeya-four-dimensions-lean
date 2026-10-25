-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.FromKatzTao
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.HalfConfig

/-!
# The `s = 1/2` bridge: extraction and endgame

`HalfExtraction`: if the bush estimate fails at `s = 1/2` (in the absolute-count form
`KatzTaoFurstenbergAt` of x0483), a `HalfConfig` exists with losses `r ^ (-A (ε₀ + η))`.
`HalfEndgame`: no `HalfConfig` exists with losses `r ^ (-κ)` for small `r`.
Together they give the fixed-exponent estimate at `s = 1/2` (`half_core`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open SP

/-- Larger loss `K` and smaller separation `c` weaken a `HalfConfig`. -/
theorem SP.HalfConfig.mono {r K K' c c' : ℝ} {n p₀ p₁ p₂ : Plane} {H Q : Finset Plane}
    {D Qh : Plane → Finset Plane}
    (h : SP.HalfConfig r K c n p₀ p₁ p₂ H Q D Qh) (hr : 0 ≤ r) (hK : 0 < K) (hKK : K ≤ K')
    (hc : c' ≤ c) : SP.HalfConfig r K' c' n p₀ p₁ p₂ H Q D Qh := by
  have hinv : K'⁻¹ ≤ K⁻¹ := inv_anti₀ hK hKK
  refine ⟨h.unit_normal, ?_, h.base_on_line, hc.trans h.base_gap, h.line_pins, h.line_sep, ?_,
    h.line_nonempty, h.line_bounded, h.pins_sep, h.pins_bounded, ?_, ?_, h.join₁, h.join₂, ?_⟩
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := h.bush p hp
    refine ⟨h1, h2, fun u hu ρ hρ => (h3 u hu ρ hρ).trans ?_⟩
    exact mul_le_mul_of_nonneg_right hKK (Real.rpow_nonneg (div_nonneg (hr.trans hρ) hr) _)
  · intro x ρ hρ
    refine (h.line_frostman x ρ hρ).trans ?_
    have hρ0 : 0 ≤ ρ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (hr.trans hρ) _
    gcongr
  · intro q hq
    exact hc.trans (h.pins_far q hq)
  · refine le_trans ?_ h.pins_many
    gcongr
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := h.line_dense p hp
    exact ⟨h1, le_trans (by gcongr) h2, h3⟩

/-- The extraction: failure of the bush estimate at `s = 1/2` gives a `HalfConfig`, for
small gain `ε₀ ≤ a` and error `η ≤ a`. -/
def HalfExtraction : Prop :=
  ∃ A a : ℝ, 0 < A ∧ 0 < a ∧ ∀ ε₀ η : ℝ, 0 < ε₀ → 0 < η → ε₀ ≤ a → η ≤ a →
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ¬ KatzTaoFurstenbergAt r (1 / 2) ε₀ η →
      ∃ (n p₀ p₁ p₂ : Plane) (H Q : Finset Plane) (D Qh : Plane → Finset Plane),
        SP.HalfConfig r (r ^ (-(A * (ε₀ + η)))) (r ^ (A * (ε₀ + η))) n p₀ p₁ p₂ H Q D Qh

/-- The endgame: `HalfConfig`s with small losses do not exist at small scales. -/
def HalfEndgame : Prop :=
  ∃ κ r₀ : ℝ, 0 < κ ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
    ∀ (n p₀ p₁ p₂ : Plane) (H Q : Finset Plane) (D Qh : Plane → Finset Plane),
      ¬ SP.HalfConfig r (r ^ (-κ)) (r ^ κ) n p₀ p₁ p₂ H Q D Qh

/-- The fixed-exponent bush estimate at `s = 1/2` from the extraction and the endgame. -/
theorem half_core (hE : HalfExtraction) (hG : HalfEndgame) :
    ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → KatzTaoFurstenbergAt r (1 / 2) ε₀ η := by
  obtain ⟨A, a, hA, ha, hext⟩ := hE
  obtain ⟨κ, r₁, hκ, hr₁, hend⟩ := hG
  set κ₂ := min κ (2 * A * a) with hκ₂
  have hκ₂p : 0 < κ₂ := lt_min hκ (by positivity)
  set ε₀ := κ₂ / (2 * A) with hε₀
  have hε₀p : 0 < ε₀ := by positivity
  have hε₀a : ε₀ ≤ a := by
    rw [hε₀, div_le_iff₀ (by positivity)]
    have := min_le_right κ (2 * A * a)
    linarith
  obtain ⟨r₂, hr₂, hext'⟩ := hext ε₀ ε₀ hε₀p hε₀p hε₀a hε₀a
  refine ⟨ε₀, ε₀, min (min r₁ r₂) 1, hε₀p, hε₀p, by positivity, ?_⟩
  intro r hr hrr
  have hr1 : r ≤ 1 := hrr.trans (min_le_right _ _)
  by_contra hfail
  obtain ⟨n, p₀, p₁, p₂, H, Q, D, Qh, hcfg⟩ :=
    hext' r hr (hrr.trans ((min_le_left _ _).trans (min_le_right _ _))) hfail
  have hAe : A * (ε₀ + ε₀) = κ₂ := by
    rw [hε₀]
    field_simp
    ring
  rw [hAe] at hcfg
  have hκle : κ₂ ≤ κ := min_le_left _ _
  have hcfg' : SP.HalfConfig r (r ^ (-κ)) (r ^ κ) n p₀ p₁ p₂ H Q D Qh :=
    hcfg.mono hr.le (Real.rpow_pos_of_pos hr _)
    (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith))
    (Real.rpow_le_rpow_of_exponent_ge hr hr1 hκle)
  exact hend r hr (hrr.trans ((min_le_left _ _).trans (min_le_left _ _))) n p₀ p₁ p₂ H Q D Qh
    hcfg'

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
