-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FactorEps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorMain

/-!
# The constant of Proposition 4.6 is `O_ε((N/ρ)^ε)`

`Kc R N ρ = 16·3456³ R³ (⌊log₂(2R/ρ)⌋₊ + 1)² e^{6√(log 384N) + 3}`: the logarithmic factor is
`O_ε(ρ^{-ε/2})` by `log x ≤ x^δ/δ`, and `e^{6√L} ≤ e^{18/ε} e^{εL/2}` by AM–GM.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

noncomputable section

theorem dyExp_add_one_le {R ρ : ℝ} (hR : 1 ≤ R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) :
    (dyExp (2 * R) ρ : ℝ) + 1 ≤ (4 * R / ρ) ^ δ / (δ * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR0 : 0 < R := by linarith
  have h4 : (1 : ℝ) ≤ 2 * R / ρ := by rw [le_div_iff₀ hρ]; linarith
  have hD : (dyExp (2 * R) ρ : ℝ) ≤ Real.logb 2 (2 * R / ρ) :=
    Nat.floor_le (Real.logb_nonneg (by norm_num) h4)
  have hlogb : Real.logb 2 (2 * R / ρ) + 1 = Real.log (4 * R / ρ) / Real.log 2 := by
    rw [Real.logb, show (4 : ℝ) * R / ρ = 2 * (2 * R / ρ) by ring,
      Real.log_mul (by norm_num) (by positivity)]
    field_simp
    ring
  have hle : Real.log (4 * R / ρ) ≤ (4 * R / ρ) ^ δ / δ :=
    Real.log_le_rpow_div (by positivity) hδ
  calc (dyExp (2 * R) ρ : ℝ) + 1 ≤ Real.logb 2 (2 * R / ρ) + 1 := by linarith
    _ = Real.log (4 * R / ρ) / Real.log 2 := hlogb
    _ ≤ (4 * R / ρ) ^ δ / δ / Real.log 2 := by gcongr
    _ = (4 * R / ρ) ^ δ / (δ * Real.log 2) := by rw [div_div]

theorem exp_six_sqrt_le {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    Real.exp (6 * Real.sqrt x) ≤ Real.exp (18 / ε) * Real.exp (ε / 2 * x) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := Real.sq_sqrt hx
  have hs0 := Real.sqrt_nonneg x
  have key : 0 ≤ ε / 2 * (Real.sqrt x - 6 / ε) ^ 2 := by positivity
  have e1 : ε / 2 * (Real.sqrt x - 6 / ε) ^ 2 = ε / 2 * x - 6 * Real.sqrt x + 18 / ε := by
    field_simp
    linear_combination ε ^ 2 * hs
  linarith

/-- **The constant of Proposition 4.6 is subpolynomial.** -/
theorem Kc_le (ε : ℝ) (hε : 0 < ε) (R : ℝ) (hR : 1 ≤ R) : ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → Kc R N ρ ≤ C * ((N : ℝ) / ρ) ^ ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set δ := ε / 4 with hδ
  have hδpos : 0 < δ := by positivity
  have hR0 : 0 < R := by linarith
  set C₀ : ℝ := 16 * 3456 ^ 3 * R ^ 3 * ((4 * R) ^ δ / (δ * Real.log 2)) ^ 2 *
    (Real.exp 3 * Real.exp (18 / ε) * (384 : ℝ) ^ (ε / 2)) with hC₀
  refine ⟨max C₀ 1, le_max_right _ _, fun N hN ρ hρ hρ1 => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNρ : (1 : ℝ) ≤ N / ρ := by rw [le_div_iff₀ hρ]; linarith
  -- the logarithmic factor
  have hD := dyExp_add_one_le hR hρ hρ1 hδpos
  have hDsq : ((dyExp (2 * R) ρ : ℝ) + 1) ^ 2 ≤
      ((4 * R) ^ δ / (δ * Real.log 2)) ^ 2 * ρ⁻¹ ^ (ε / 2) := by
    have h1 : ((dyExp (2 * R) ρ : ℝ) + 1) ^ 2 ≤ ((4 * R / ρ) ^ δ / (δ * Real.log 2)) ^ 2 := by
      gcongr
    refine h1.trans (le_of_eq ?_)
    rw [div_pow, div_pow, Real.div_rpow (by positivity) hρ.le, div_pow,
      ← Real.rpow_natCast ((ρ : ℝ) ^ δ) 2, ← Real.rpow_mul hρ.le, Real.inv_rpow hρ.le,
      ← Real.rpow_neg hρ.le]
    have : δ * ((2 : ℕ) : ℝ) = ε / 2 := by rw [hδ]; push_cast; ring
    rw [this]
    rw [Real.rpow_neg hρ.le]
    field_simp
  -- the exponential factor
  have hlogN : 0 ≤ Real.log (384 * N) := Real.log_nonneg (by nlinarith)
  have hexp : Real.exp (6 * lam N + 3) ≤
      Real.exp 3 * Real.exp (18 / ε) * ((384 : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) := by
    rw [Real.exp_add, lam]
    have h1 := exp_six_sqrt_le hlogN hε
    have h2 : Real.exp (ε / 2 * Real.log (384 * N)) = (384 : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by
      rw [mul_comm, ← Real.rpow_def_of_pos (by positivity), Real.mul_rpow (by norm_num) hNpos.le]
    rw [h2] at h1
    have h3 := Real.exp_pos 3
    nlinarith
  -- combine
  have hpow : ρ⁻¹ ^ (ε / 2) * (N : ℝ) ^ (ε / 2) ≤ ((N : ℝ) / ρ) ^ ε := by
    rw [← Real.mul_rpow (by positivity) hNpos.le, inv_mul_eq_div]
    exact Real.rpow_le_rpow_of_exponent_le hNρ (by linarith)
  have hρpow : 0 ≤ ρ⁻¹ ^ (ε / 2) := by positivity
  have hNpow : 0 ≤ (N : ℝ) ^ (ε / 2) := by positivity
  have h384 : 0 ≤ (384 : ℝ) ^ (ε / 2) := by positivity
  calc Kc R N ρ = 16 * 3456 ^ 3 * R ^ 3 * ((dyExp (2 * R) ρ : ℝ) + 1) ^ 2 *
        Real.exp (6 * lam N + 3) := rfl
    _ ≤ 16 * 3456 ^ 3 * R ^ 3 * (((4 * R) ^ δ / (δ * Real.log 2)) ^ 2 * ρ⁻¹ ^ (ε / 2)) *
        (Real.exp 3 * Real.exp (18 / ε) * ((384 : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2))) := by
        gcongr
    _ = C₀ * (ρ⁻¹ ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) := by rw [hC₀]; ring
    _ ≤ max C₀ 1 * ((N : ℝ) / ρ) ^ ε := by
        gcongr
        · exact le_max_left _ _

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
