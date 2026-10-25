import Mathlib

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open scoped ENNReal

/-- Absorb the relative anchor error and the absolute sublevel error before
paying the factor-two source-bin choice loss. -/
theorem retained_mass_floor {κ : ℝ} (hκ : 0 < κ) {M S e r : ℝ≥0∞}
    (hM : M ≠ ∞) (hfloor : ENNReal.ofReal κ⁻¹ ≤ M)
    (hmass : M ≤ 2 * S + e + r * M)
    (hrel : r ≤ ENNReal.ofReal (1 / 4 : ℝ))
    (herr : e ≤ ENNReal.ofReal (κ⁻¹ / 4)) :
    ENNReal.ofReal (4 * κ)⁻¹ ≤ S := by
  by_cases hS : S = ∞
  · simp [hS]
  have hSt : S ≠ ∞ := hS
  have hr : r ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrel
  have he : e ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top herr
  have h2S : (2 : ℝ≥0∞) * S ≠ ∞ := by finiteness
  have h2Se : (2 : ℝ≥0∞) * S + e ≠ ∞ := by finiteness
  have hrM : r * M ≠ ∞ := by finiteness
  have hR : (2 : ℝ≥0∞) * S + e + r * M ≠ ∞ := by finiteness
  have hmreal := ENNReal.toReal_mono hR hmass
  have hrepr : ((2 : ℝ≥0∞) * S + e + r * M).toReal =
      2 * S.toReal + e.toReal + r.toReal * M.toReal := by
    rw [ENNReal.toReal_add h2Se hrM, ENNReal.toReal_add h2S he]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  rw [hrepr] at hmreal
  have hfreal : κ⁻¹ ≤ M.toReal := (ENNReal.ofReal_le_iff_le_toReal hM).mp hfloor
  have hrreal : r.toReal ≤ 1 / 4 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hrel
    norm_num at hh ⊢
    exact hh
  have hereal : e.toReal ≤ κ⁻¹ / 4 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top herr
    rwa [ENNReal.toReal_ofReal (by positivity)] at hh
  have hrelmul := mul_le_mul_of_nonneg_right hrreal (ENNReal.toReal_nonneg : 0 ≤ M.toReal)
  have hret : κ⁻¹ / 4 ≤ S.toReal := by nlinarith
  apply (ENNReal.ofReal_le_iff_le_toReal hSt).mpr
  simpa only [mul_inv_rev, div_eq_mul_inv] using hret

/-- The absolute sublevel error follows from the same numerical gap that
controls the relative anchor error. -/
theorem absolute_error_le {κ A : ℝ} (hκ : 0 < κ) (hA : 2 ≤ A)
    (hrel : κ / A ≤ 1 / 4) : 2 / A ^ 2 ≤ κ⁻¹ / 4 := by
  have hA0 : 0 < A := by linarith
  have hgap : κ ≤ (1 / 4 : ℝ) * A := (div_le_iff₀ hA0).mp hrel
  have hsquare : 2 * A ≤ A ^ 2 := by nlinarith
  have hgap' : 8 * κ ≤ A ^ 2 := by linarith
  have hh : 2 / A ^ 2 ≤ 1 / (4 * κ) :=
    (div_le_div_iff₀ (sq_pos_of_pos hA0) (by positivity)).mpr (by nlinarith)
  simpa only [one_div, mul_inv_rev, div_eq_mul_inv, one_mul] using hh

theorem power_absolute_error_le {N a κ : ℝ} (hN : 0 < N) (hκ : 0 < κ)
    (hA : 2 ≤ N ^ a) (hrel : κ * (N ^ a)⁻¹ ≤ 1 / 4) :
    2 * N ^ (-(2 * a)) ≤ κ⁻¹ / 4 := by
  have hp : (N ^ a) ^ 2 = N ^ (2 * a) := by
    rw [pow_two, ← Real.rpow_add hN]
    congr 1
    ring
  have hn : N ^ (-(2 * a)) = ((N ^ a) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hN.le, hp]
  rw [hn]
  simpa only [div_eq_mul_inv] using absolute_error_le hκ hA (by simpa only [div_eq_mul_inv] using hrel)

end Submission.Obl.k4_pair_bin_atlas_assembly
