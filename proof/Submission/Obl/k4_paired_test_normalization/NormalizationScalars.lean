-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/NormalizationScalars.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.NormalizationNumerics
import Submission.Obl.k4_paired_test_normalization.FrozenDensity

namespace Submission.Obl.k4_paired_test_normalization.NormalizationStep

open Filter

lemma normalization_cross_eq {N δv a : ℝ} (hN : 0 < N) (hδ : δv ≠ 0) :
    2 * (δv⁻¹ * N ^ (-(30 * a))) * (δv * N ^ a) = 2 * N ^ (-(29 * a)) := by
  calc
    _ = 2 * (δv⁻¹ * δv) * (N ^ (-(30 * a)) * N ^ a) := by ring
    _ = 2 * N ^ (-(30 * a) + a) := by
      rw [inv_mul_cancel₀ hδ, mul_one, ← Real.rpow_add hN]
    _ = 2 * N ^ (-(29 * a)) := by congr 2 <;> ring

/-- A fixed complexity exponent absorbs the critical-center replacement, and
all value/derivative ceilings fit under loss exponent `100 a`. -/
theorem eventually_normalization_scalars {N : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) {a L : ℝ} (ha : 0 < a) (hL : 0 < L) (M : ℕ) :
    ∃ M' : ℕ, M ≤ M' ∧ ∀ᶠ k in atTop,
      δ (N k) L ≤ 1 ∧
      max (N k ^ M) (2 * N k ^ M / ((δ (N k) L)⁻¹ * N k ^ (-(30 * a)))) ≤ N k ^ M' ∧
      max (δ (N k) L * N k ^ a)
        (N k ^ a / ((δ (N k) L)⁻¹ * N k ^ (-(30 * a)))) ≤
          δ (N k) L * N k ^ (100 * a) ∧
      max (N k ^ a) 1 ≤ N k ^ (100 * a) ∧
      (δ (N k) L)⁻¹ * N k ^ (-(30 * a)) ≤ (δ (N k) L)⁻¹ := by
  let M' := M + ⌈30 * a⌉₊ + 1
  have hMM' : M ≤ M' := by dsimp [M']; omega
  have hgap : (M : ℝ) + 30 * a < (M' : ℝ) := by
    have hc := Nat.le_ceil (30 * a)
    dsimp [M']
    push_cast
    linarith
  have hcoef := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt hgap 2
  have hδsmall := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -L < (0 : ℝ) by linarith) 2
  refine ⟨M', hMM', ?_⟩
  filter_upwards [hcoef, hδsmall] with k hcoefk hδk
  have hNk : 1 ≤ N k := by linarith [hN k]
  have hNp : 0 < N k := by linarith
  have hδp := δ_pos (N k) L
  have hδ1 : δ (N k) L ≤ 1 := by
    have hb := (δ_bounds (N := N k) (by linarith [hN k]) L).2
    simp only [Real.rpow_zero] at hδk
    linarith
  have hinv : (((δ (N k) L)⁻¹ * N k ^ (-(30 * a)))⁻¹) =
      δ (N k) L * N k ^ (30 * a) := by
    rw [mul_inv_rev, Real.rpow_neg hNp.le, inv_inv, inv_inv]
    ring
  have hmon : N k ^ M ≤ N k ^ M' := pow_le_pow_right₀ hNk hMM'
  refine ⟨hδ1, max_le hmon ?_, max_le ?_ ?_, max_le ?_ ?_, ?_⟩
  · rw [div_eq_mul_inv, hinv]
    calc
      2 * N k ^ M * (δ (N k) L * N k ^ (30 * a)) ≤
          2 * N k ^ M * (1 * N k ^ (30 * a)) := by gcongr
      _ = 2 * N k ^ ((M : ℝ) + 30 * a) := by
        rw [Real.rpow_add hNp, Real.rpow_natCast]
        ring
      _ ≤ N k ^ M' := by simpa only [Real.rpow_natCast] using hcoefk.le
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNk (by linarith)) hδp.le
  · rw [div_eq_mul_inv, hinv]
    calc
      N k ^ a * (δ (N k) L * N k ^ (30 * a)) = δ (N k) L * N k ^ (31 * a) := by
        rw [show 31 * a = a + 30 * a by ring, Real.rpow_add hNp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hNk (by linarith)) hδp.le
  · exact Real.rpow_le_rpow_of_exponent_le hNk (by linarith)
  · exact Real.one_le_rpow hNk (by linarith)
  · exact mul_le_of_le_one_right (inv_nonneg.mpr hδp.le)
      (Real.rpow_le_one_of_one_le_of_nonpos hNk (by linarith))

end Submission.Obl.k4_paired_test_normalization.NormalizationStep
