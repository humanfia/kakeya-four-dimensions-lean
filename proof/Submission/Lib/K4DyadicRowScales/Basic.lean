/-
Adapted from: here:o265
Original arithmetic and topology proofs by x1027.
-/
import Mathlib

/-!
# Dyadic scales for the original four-dimensional row estimate

The fine and coarse meshes are `2^(-3n)` and `2^(-2n)`. Thus the coarse scale is exactly the
fine scale to the power `2/3`, and both coarsenings use the same integer number of steps.
The scale choices do not depend on a time exponent or on a trajectory type.
-/

namespace Submission.Lib.K4DyadicRowScales

open Filter

noncomputable section

/-- The common dyadic unit. -/
def unit (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

/-- The fine physical mesh. -/
def mesh (n : ℕ) : ℝ := unit n ^ 3

/-- The isotropic coarse mesh. -/
def coarse (n : ℕ) : ℝ := unit n ^ 2

lemma unit_pos (n : ℕ) : 0 < unit n := by unfold unit; positivity

lemma unit_le_one (n : ℕ) : unit n ≤ 1 := by
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

lemma mesh_pos (n : ℕ) : 0 < mesh n := pow_pos (unit_pos n) _

lemma coarse_pos (n : ℕ) : 0 < coarse n := pow_pos (unit_pos n) _

lemma mesh_eq_zpow (n : ℕ) : mesh n = (2 : ℝ) ^ (-(3 * (n : ℤ))) := by
  rw [show 3 * (n : ℤ) = ((n * 3 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  simp only [mesh, unit, inv_pow, pow_mul]

lemma coarse_eq_zpow (n : ℕ) : coarse n = (2 : ℝ) ^ (-(2 * (n : ℤ))) := by
  rw [show 2 * (n : ℤ) = ((n * 2 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  simp only [coarse, unit, inv_pow, pow_mul]

lemma coarse_eq_mesh_rpow (n : ℕ) : coarse n = mesh n ^ ((2 : ℝ) / 3) := by
  rw [mesh, ← Real.rpow_natCast, ← Real.rpow_mul (unit_pos n).le]
  norm_num [coarse, Real.rpow_natCast]

lemma coarse_eq_mesh_mul_pow (n : ℕ) : coarse n = mesh n * (2 : ℝ) ^ n := by
  have hn : (2 : ℝ) ^ n ≠ 0 := by positivity
  unfold coarse mesh unit
  field_simp

lemma mesh_le_coarse (n : ℕ) : mesh n ≤ coarse n := by
  unfold mesh coarse
  nlinarith [unit_pos n, unit_le_one n, sq_nonneg (unit n)]

lemma coarse_le_one (n : ℕ) : coarse n ≤ 1 := by
  exact pow_le_one₀ (unit_pos n).le (unit_le_one n)

lemma tendsto_unit : Tendsto unit atTop (nhds 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

lemma tendsto_mesh : Tendsto mesh atTop (nhds 0) := by
  change Tendsto (fun n => unit n ^ 3) atTop (nhds 0)
  simpa using tendsto_unit.pow 3

lemma tendsto_coarse : Tendsto coarse atTop (nhds 0) := by
  change Tendsto (fun n => unit n ^ 2) atTop (nhds 0)
  simpa using tendsto_unit.pow 2

/-- A prescribed lifting accuracy can be reduced until the conditioned-direction estimate
holds, without using any mesh or trajectory data. -/
theorem exists_lift_radius {B target : ℝ} (hB : 1 ≤ B) (htarget : 0 < target) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ target ∧ 36 * B ^ 3 * (B * ρ) ≤ 1 := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨min target (36 * B ^ 4)⁻¹, lt_min htarget (by positivity), min_le_left _ _, ?_⟩
  have hle := min_le_right target (36 * B ^ 4)⁻¹
  have hmul := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 36 * B ^ 4)
  rw [mul_inv_cancel₀ (by positivity : (36 : ℝ) * B ^ 4 ≠ 0)] at hmul
  nlinarith

/-- Once the lifting radius is fixed, every sufficiently fine dyadic pair satisfies all
mesh inequalities in the original anisotropic row estimate. -/
theorem eventually_row_budgets {B C dimension fraction massError ρ : ℝ}
    (hB : 1 ≤ B) (hdimension : dimension < 1)
    (hfraction : 0 < fraction) (hmassError : 0 < massError) (hρ : 0 < ρ) :
    ∀ᶠ n : ℕ in atTop,
      0 < mesh n ∧ mesh n ≤ coarse n ∧ coarse n ≤ 1 ∧
      coarse n = mesh n ^ ((2 : ℝ) / 3) ∧
      coarse n = mesh n * (2 : ℝ) ^ n ∧
      8 * B * coarse n ^ 2 < mesh n ∧
      32 * B * coarse n ≤ ρ / 2 ∧
      256 * C ^ 3 * B ^ 9 * mesh n ^ ((1 - dimension) / 3) ≤
        (fraction * ρ / 4) ^ 4 * massError ^ 4 := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hgap : 0 < (1 - dimension) / 3 := by linarith
  have hquad : ∀ᶠ n : ℕ in atTop, 8 * B * unit n < 1 := by
    apply (show Tendsto (fun n => 8 * B * unit n) atTop (nhds 0) from
      by simpa using tendsto_unit.const_mul (8 * B)).eventually_lt_const
    norm_num
  have hdir : ∀ᶠ n : ℕ in atTop, 32 * B * coarse n < ρ / 2 := by
    apply (show Tendsto (fun n => 32 * B * coarse n) atTop (nhds 0) from
      by simpa using tendsto_coarse.const_mul (32 * B)).eventually_lt_const
    positivity
  have hpow : Tendsto (fun n => mesh n ^ ((1 - dimension) / 3)) atTop (nhds 0) := by
    simpa only [Real.zero_rpow (ne_of_gt hgap)] using
      tendsto_mesh.rpow_const (Or.inr hgap.le)
  have hbudget : ∀ᶠ n : ℕ in atTop,
      256 * C ^ 3 * B ^ 9 * mesh n ^ ((1 - dimension) / 3) <
        (fraction * ρ / 4) ^ 4 * massError ^ 4 := by
    apply (show Tendsto (fun n => 256 * C ^ 3 * B ^ 9 * mesh n ^ ((1 - dimension) / 3))
        atTop (nhds 0) from by simpa using hpow.const_mul (256 * C ^ 3 * B ^ 9)).eventually_lt_const
    positivity
  filter_upwards [hquad, hdir, hbudget] with n hquad hdir hbudget
  refine ⟨mesh_pos n, mesh_le_coarse n, coarse_le_one n, coarse_eq_mesh_rpow n,
    coarse_eq_mesh_mul_pow n, ?_, hdir.le, hbudget.le⟩
  have h := mul_lt_mul_of_pos_right hquad (mesh_pos n)
  change 8 * B * unit n * unit n ^ 3 < 1 * unit n ^ 3 at h
  change 8 * B * (unit n ^ 2) ^ 2 < unit n ^ 3
  nlinarith [h]

/-- The lifting radius is chosen before the scale cutoff. Arbitrarily fine dyadic scales
are available, so an independently specified upper mesh bound can also be imposed. -/
theorem exists_dyadic_row_scales {B C dimension fraction massError target upper : ℝ}
    (hB : 1 ≤ B) (hdimension : dimension < 1) (hfraction : 0 < fraction)
    (hmassError : 0 < massError) (htarget : 0 < target) (hupper : 0 < upper) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ target ∧ 36 * B ^ 3 * (B * ρ) ≤ 1 ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        0 < mesh n ∧ mesh n ≤ coarse n ∧ coarse n ≤ 1 ∧ coarse n ≤ upper ∧
        coarse n = mesh n ^ ((2 : ℝ) / 3) ∧
        coarse n = mesh n * (2 : ℝ) ^ n ∧
        8 * B * coarse n ^ 2 < mesh n ∧
        32 * B * coarse n ≤ ρ / 2 ∧
        256 * C ^ 3 * B ^ 9 * mesh n ^ ((1 - dimension) / 3) ≤
          (fraction * ρ / 4) ^ 4 * massError ^ 4 := by
  obtain ⟨ρ, hρ, hρtarget, hsmall⟩ := exists_lift_radius hB htarget
  refine ⟨ρ, hρ, hρtarget, hsmall, eventually_atTop.mp ?_⟩
  filter_upwards [eventually_row_budgets (C := C) hB hdimension hfraction hmassError hρ,
      tendsto_coarse.eventually_lt_const hupper] with n hn hupper
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hupper.le, hn.2.2.2⟩

end

end Submission.Lib.K4DyadicRowScales
