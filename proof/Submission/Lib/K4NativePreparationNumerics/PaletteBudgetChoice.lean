/-
Adapted from: here:o204
Original file: Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PaletteBudgetChoice.lean.
Any earlier attribution is retained below.
-/
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Explicit actual light-parent and palette thresholds retain15/16 of the
fixed prepared law once the likelihood omission is at most1/128. -/

namespace Submission.Lib.K4NativePreparationNumerics

open scoped ENNReal

noncomputable def lightParentThreshold (κ : ℝ) : ENNReal :=
  ENNReal.ofReal ((1024 * κ)⁻¹)

noncomputable def palettePruningThreshold (K : ℕ) : ℝ := (128 * (K : ℝ))⁻¹

theorem lightParentThreshold_ne_zero {κ : ℝ} (hκ : 0 < κ) : lightParentThreshold κ ≠ 0 :=
  ENNReal.ofReal_ne_zero_iff.mpr (by positivity)

theorem lightParentThreshold_ne_top (κ : ℝ) : lightParentThreshold κ ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem palettePruningThreshold_pos {K : ℕ} (hK : 1 ≤ K) : 0 < palettePruningThreshold K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  unfold palettePruningThreshold
  positivity

theorem lightParentThreshold_cost {κ : ℝ} (hκ : 0 < κ) :
    lightParentThreshold κ * ENNReal.ofReal (8 * κ) = ENNReal.ofReal (1 / 128 : ℝ) := by
  have heq : (1024 * κ)⁻¹ * (8 * κ) = (1 / 128 : ℝ) := by
    field_simp [hκ.ne']
    norm_num
  rw [lightParentThreshold, ← ENNReal.ofReal_mul (by positivity), heq]

theorem palettePruningThreshold_cost {K : ℕ} (hK : 1 ≤ K) :
    palettePruningThreshold K * K = (1 / 128 : ℝ) := by
  have hK0 : (K : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK))
  unfold palettePruningThreshold
  field_simp [hK0]

theorem native_palette_budget_choices {κ : ℝ} (hκ : 0 < κ) {K : ℕ} (hK : 1 ≤ K) :
    ENNReal.ofReal (1 / 128 : ℝ) +
      (lightParentThreshold κ * ENNReal.ofReal (8 * κ) +
        ENNReal.ofReal (palettePruningThreshold K * K)) ≤ ENNReal.ofReal (1 / 16 : ℝ) := by
  rw [lightParentThreshold_cost hκ, palettePruningThreshold_cost hK,
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 128) (by norm_num : (0 : ℝ) ≤ 1 / 128),
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 128) (by norm_num : (0 : ℝ) ≤ 1 / 128 + 1 / 128)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

theorem lightParentThreshold_inv {κ : ℝ} (hκ : 0 < κ) :
    (lightParentThreshold κ)⁻¹ = ENNReal.ofReal (1024 * κ) := by
  rw [lightParentThreshold, ENNReal.ofReal_inv_of_pos (by positivity : 0 < 1024 * κ), inv_inv]

theorem angular_threshold_inv {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 0 < m) :
    (ENNReal.ofReal ((8 * (m : ℝ) * κ ^ 2)⁻¹))⁻¹ = ENNReal.ofReal (8 * (m : ℝ) * κ ^ 2) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [ENNReal.ofReal_inv_of_pos (by positivity : 0 < 8 * (m : ℝ) * κ ^ 2), inv_inv]

theorem native_angular_cap_coefficient {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx : 0 ≤ x) :
    100 * ((ENNReal.ofReal x * (ENNReal.ofReal ((8 * (m : ℝ) * κ ^ 2)⁻¹))⁻¹) *
      (lightParentThreshold κ)⁻¹) = ENNReal.ofReal (819200 * (m : ℝ) * κ ^ 3 * x) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [angular_threshold_inv hκ hm, lightParentThreshold_inv hκ,
    ← ENNReal.ofReal_ofNat 100, ← ENNReal.ofReal_mul hx,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ x * (8 * (m : ℝ) * κ ^ 2)),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
  congr 1
  ring

end Submission.Lib.K4NativePreparationNumerics
