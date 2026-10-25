import Submission.Obl.k4_general_wide_layer_offset_comparison.Return
import Submission.Obl.k4_quadratic_mesh_coefficient_calibration.RawGridCalibration
import Submission.Obl.k4_scalar_initial_true_horizon.InitialAsymptotic

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/GridCalibration.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory MvPolynomial Set Filter
open scoped ENNReal

noncomputable section

/-- One sufficiently fine primitive mesh calibrates a quadratic from a
polynomial original mass floor. There is no continuous base domination premise. -/
theorem eventually_quadratic_grid_calibration {N : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    {A : ℝ} (hA : 0 < A) :
    ∀ᶠ k in atTop, ∀ (Ω : Type*) [MeasurableSpace Ω]
      (σ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (G : MvPolynomial (Fin 3) ℝ),
      G.totalDegree ≤ 2 →
      ENNReal.ofReal (N k ^ (-A)) ≤ σ univ →
      (∀ q : Fin 3 → ℤ,
        σ {ω | Submission.Lib.K4CommonLocalChoice.cell
          (N k ^ (-(32 * A))) (Z ω) = q} ≤
          ENNReal.ofReal (N k ^ A * (N k ^ (-(32 * A))) ^ 3)) →
      (∀ᵐ ω ∂σ, (∀ j, |Z ω j| ≤ N k ^ A) ∧ |eval (Z ω) G| ≤ N k ^ A) →
      ∀ e, |G.coeff e| ≤ N k ^ (32 * A) := by
  obtain ⟨C, L, hC, hL, hcal⟩ :=
    Submission.Obl.k4_quadratic_mesh_coefficient_calibration.exists_raw_coefficient_bound_from_original_grid 2
  let B := (27 : ℝ) * (2 * 27 * C * (96 * 512) ^ 6)
  let V := (2 : ℝ) * L * 27 * C * (96 * 512) ^ 6 / 8
  filter_upwards [Submission.Obl.k4_scalar_initial_true_horizon.eventually_const_le_rpow
    hNt hA (max B (2 * V))] with k hk
  intro Ω _ σ Z G hG hmass hcap htrace e
  have hNp : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  let X := N k ^ A
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 hA.le
  have hX : 0 < X := by linarith
  have hB : B ≤ X := (le_max_left _ _).trans hk
  have hV : 2 * V ≤ X := (le_max_right _ _).trans hk
  have hmesh : N k ^ (-(32 * A)) = (X ^ 32)⁻¹ := by
    rw [Real.rpow_neg hNp.le]
    congr 1
    dsimp [X]
    rw [← Real.rpow_mul_natCast hNp.le]
    congr 1
    ring
  have hX32 : 1 ≤ X ^ 32 := one_le_pow₀ hX1
  have hhm : 0 < (X ^ 32)⁻¹ := by positivity
  have hhH : (X ^ 32)⁻¹ ≤ X := by
    calc
      (X ^ 32)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hX32
      _ ≤ X := hX1
  have hmβ : X⁻¹ ≤ X * (8 * X) ^ 3 := by
    have hinv : X⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hX1
    have hr1 : 1 ≤ (8 * X) ^ 3 := one_le_pow₀ (by linarith)
    have hr : 1 ≤ X * (8 * X) ^ 3 := by nlinarith
    exact hinv.trans hr
  have hnum :
      2 * L * (27 : ℝ) * C * (96 / (X⁻¹ / (X * (8 * X) ^ 3))) ^ 6 *
        ((X ^ 32)⁻¹ / (8 * X)) = V / X ^ 3 := by
    dsimp [V]
    field_simp [hX.ne']
    <;> ring
  have hsmall :
      2 * L * (27 : ℝ) * C * (96 / (X⁻¹ / (X * (8 * X) ^ 3))) ^ 6 *
        ((X ^ 32)⁻¹ / (8 * X)) ≤ 1 / 2 := by
    rw [hnum, div_le_iff₀ (pow_pos hX 3)]
    have h3 : X ≤ X ^ 3 := le_self_pow₀ hX1 (by norm_num)
    linarith
  have hc := hcal Ω σ Z G hG X ((X ^ 32)⁻¹) X⁻¹ X X hX1 hhm hhH
    (inv_pos.mpr hX) hX hmβ hX.le
    (by simpa only [Real.rpow_neg hNp.le] using hmass)
    (by simpa only [hmesh] using hcap) htrace
  norm_num only [Nat.reduceAdd, Nat.reducePow, Nat.cast_ofNat, Nat.reduceMul] at hc
  have hbound := hc hsmall e
  have hnum' :
      (27 : ℝ) * (54 * C * (96 / (X⁻¹ / (X * (8 * X) ^ 3))) ^ 6 * X) =
        B * X ^ 31 := by
    dsimp [B]
    field_simp [hX.ne']
    <;> ring
  rw [hnum'] at hbound
  calc
    |G.coeff e| ≤ B * X ^ 31 := hbound
    _ ≤ X * X ^ 31 := mul_le_mul_of_nonneg_right hB (by positivity)
    _ = N k ^ (32 * A) := by
      rw [show X * X ^ 31 = X ^ 32 by ring]
      dsimp [X]
      rw [← Real.rpow_mul_natCast hNp.le]
      congr 1
      ring

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
