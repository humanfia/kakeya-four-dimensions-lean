-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/PolynomialNarrowMass.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.NarrowMassComparison

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.PolynomialNarrowMass

theorem kappa_power_mass_le_loss_fraction {N κ α fraction loss : ℝ}
    (hκ : 0 ≤ κ) (hfraction : 0 < fraction) (hloss : 0 < loss)
    (hlarge : 8 * loss / fraction ≤ N ^ α) :
    (κ * N ^ α)⁻¹ / 8 ≤ (κ * loss)⁻¹ * fraction / 64 := by
  have hlarge' : 8 / (fraction / loss) ≤ N ^ α := by
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc] using hlarge
  calc
    _ ≤ κ⁻¹ * (fraction / loss) / 64 :=
      NarrowMassComparison.kappa_power_mass_le_fraction hκ
        (div_pos hfraction hloss) hlarge'
    _ = (κ * loss)⁻¹ * fraction / 64 := by
      rw [mul_inv_rev]
      ring

theorem kappa_power_mass_le_polynomial_fraction {N κ α fraction : ℝ} (p : ℕ)
    (hκ : 0 < κ) (hfraction : 0 < fraction)
    (hlarge : 8 * κ ^ p / fraction ≤ N ^ α) :
    (κ * N ^ α)⁻¹ / 8 ≤ (κ ^ (p + 1))⁻¹ * fraction / 64 := by
  have hlarge' : 8 / (fraction / κ ^ p) ≤ N ^ α := by
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc] using hlarge
  calc
    _ ≤ κ⁻¹ * (fraction / κ ^ p) / 64 :=
      NarrowMassComparison.kappa_power_mass_le_fraction hκ.le
        (div_pos hfraction (pow_pos hκ p)) hlarge'
    _ = (κ ^ (p + 1))⁻¹ * fraction / 64 := by
      rw [pow_succ, mul_inv_rev]
      ring

/-- The cutoff and exponent are chosen before the path factor. Any fixed
polynomial loss in that factor still supplies the requested original mass. -/
theorem eventually_kappa_power_mass_le_polynomial_fraction
    {N : ℕ → ℝ} {α fraction : ℝ} (p : ℕ)
    (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hα : 0 < α) (hfraction : 0 < fraction) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in Filter.atTop, ∀ κ : ℝ,
      0 < κ → κ ≤ N k ^ σ →
      (κ * N k ^ α)⁻¹ / 8 ≤ (κ ^ (p + 1))⁻¹ * fraction / 64 := by
  let σ : ℝ := α / (2 * ((p : ℝ) + 1))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσp : σ * p ≤ α / 2 := by
    dsimp [σ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((p : ℝ) + 1))).mpr
    nlinarith [show (0 : ℝ) ≤ (p : ℝ) from Nat.cast_nonneg p]
  have hhalf : 0 < α / 2 := by linarith
  have hlarge : ∀ᶠ k in Filter.atTop, 8 / fraction ≤ N k ^ (α / 2) :=
    ((tendsto_rpow_atTop hhalf).comp hN).eventually
      (Filter.eventually_ge_atTop (8 / fraction))
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hlarge, hN.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with k hk hkN
  intro κ hκ hκN
  have hNk : 0 ≤ N k := le_trans (by norm_num) hkN
  have hκp : κ ^ p ≤ N k ^ (α / 2) := by
    calc
      _ ≤ (N k ^ σ) ^ p := pow_le_pow_left₀ hκ.le hκN p
      _ = N k ^ (σ * (p : ℝ)) := (Real.rpow_mul_natCast hNk σ p).symm
      _ ≤ N k ^ (α / 2) := Real.rpow_le_rpow_of_exponent_le hkN hσp
  apply kappa_power_mass_le_polynomial_fraction p hκ hfraction
  calc
    8 * κ ^ p / fraction = (8 / fraction) * κ ^ p := by ring
    _ ≤ (N k ^ (α / 2)) * (N k ^ (α / 2)) :=
      mul_le_mul hk hκp (pow_nonneg hκ.le p) (Real.rpow_nonneg hNk _)
    _ = N k ^ α := by
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hkN)]
      congr 1
      ring

/-- A further power loss can use half the requested slack. The same cutoff
works for every subsequent path factor and every such power loss. -/
theorem eventually_kappa_power_mass_le_polynomial_power_fraction
    {N : ℕ → ℝ} {α fraction : ℝ} (p : ℕ)
    (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hα : 0 < α) (hfraction : 0 < fraction) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in Filter.atTop, ∀ κ : ℝ,
      0 < κ → κ ≤ N k ^ σ → ∀ β : ℝ, β ≤ α / 2 →
      (κ * N k ^ α)⁻¹ / 8 ≤ (κ ^ (p + 1) * N k ^ β)⁻¹ * fraction / 64 := by
  obtain ⟨σ, hσ, hmass⟩ := eventually_kappa_power_mass_le_polynomial_fraction p hN
    (by linarith : 0 < α / 2) hfraction
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hmass, hN.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with k hk hkN
  intro κ hκ hκN β hβ
  have hNk : 0 < N k := lt_of_lt_of_le zero_lt_one hkN
  have hpower : N k ^ (α / 2) * N k ^ β ≤ N k ^ α := by
    rw [← Real.rpow_add hNk]
    exact Real.rpow_le_rpow_of_exponent_le hkN (by linarith)
  have hmul : κ * (N k ^ (α / 2) * N k ^ β) ≤ κ * N k ^ α :=
    mul_le_mul_of_nonneg_left hpower hκ.le
  calc
    _ ≤ (κ * (N k ^ (α / 2) * N k ^ β))⁻¹ / 8 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hmul
    _ = ((κ * N k ^ (α / 2))⁻¹ / 8) * (N k ^ β)⁻¹ := by
      simp only [mul_inv_rev]
      ring
    _ ≤ ((κ ^ (p + 1))⁻¹ * fraction / 64) * (N k ^ β)⁻¹ :=
      mul_le_mul_of_nonneg_right (hk κ hκ hκN) (by positivity)
    _ = (κ ^ (p + 1) * N k ^ β)⁻¹ * fraction / 64 := by
      rw [mul_inv_rev]
      ring

end Submission.Obl.k4_isotropic_path_improvement.Repair.PolynomialNarrowMass
