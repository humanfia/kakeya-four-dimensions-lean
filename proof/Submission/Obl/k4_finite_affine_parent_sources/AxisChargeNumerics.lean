-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- Integer list and velocity-cell ceilings cost fixed powers of the
original path slack, uniformly in the number of labels. -/
theorem axis_integer_budgets (κ ρ u : ℝ) (hκ : 1 ≤ κ) (hρ : 0 ≤ ρ)
    (hu : 0 < u) (hρu : ρ ≤ u) :
    ∃ Kc M : ℕ, κ ≤ Kc ∧ (Kc : ℝ) ≤ 2 * κ ∧
      (4 * κ ^ 2 * ρ / u + 4) ^ 2 ≤ M ∧ (M : ℝ) ≤ 65 * κ ^ 4 := by
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  have hκ2 : (1 : ℝ) ≤ κ ^ 2 := one_le_pow₀ hκ
  have hκ4 : (1 : ℝ) ≤ κ ^ 4 := one_le_pow₀ hκ
  have hratio : ρ / u ≤ 1 := (div_le_one hu).mpr hρu
  have hprod : 4 * κ ^ 2 * (ρ / u) ≤ 4 * κ ^ 2 :=
    mul_le_of_le_one_right (by positivity) hratio
  have hwidth : 4 * κ ^ 2 * ρ / u + 4 ≤ 8 * κ ^ 2 := by
    have heq : 4 * κ ^ 2 * ρ / u = 4 * κ ^ 2 * (ρ / u) := by ring
    rw [heq]
    linarith
  have hcells : (4 * κ ^ 2 * ρ / u + 4) ^ 2 ≤ 64 * κ ^ 4 := by
    calc
      _ ≤ (8 * κ ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hwidth 2
      _ = _ := by ring
  refine ⟨⌈κ⌉₊, ⌈64 * κ ^ 4⌉₊, Nat.le_ceil κ, ?_,
    hcells.trans (Nat.le_ceil _), ?_⟩
  · have h := Nat.ceil_lt_add_one hκ0
    linarith
  · have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 64 * κ ^ 4)
    linarith

/-- The terminal angular ceiling divided by the terminal pure floor
has the common power used by the original deficient-axis charge. -/
theorem axis_angular_reference_ratio {N : ℝ} (hN : 0 < N) (fL S a τ : ℝ) :
    ENNReal.ofReal (N ^ (-fL - S * a + τ)) /
      ENNReal.ofReal (N ^ (-fL - τ)) =
      ENNReal.ofReal (N ^ (-S * a + 2 * τ)) := by
  rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hN _)]
  congr 1
  rw [← Real.rpow_sub hN]
  congr 1
  ring

end

end Submission.Obl.k4_finite_affine_parent_sources
