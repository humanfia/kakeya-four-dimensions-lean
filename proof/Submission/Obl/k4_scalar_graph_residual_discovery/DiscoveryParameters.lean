/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file DiscoveryParameters.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

/-- Choose the finite grids and original-reference loss exponents after the
higher-jet constant budget. The angular exponent `S` controls separation;
the fixed coarse/floor scale enters only through the natural number `C`. -/
theorem exists_discovery_parameters (C : ℕ) {α S : ℝ} (hα : 0 < α) (hS : 0 < S) :
    ∃ J₂ J₁ : ℕ, 1 ≤ J₂ ∧ 1 ≤ J₁ ∧ ∃ ω τ : ℝ,
      0 < ω ∧ 0 < τ ∧ ω ≤ 1 ∧ τ ≤ 1 ∧ S * τ = 4 * ω ∧
      (3 * ω + 2 / (J₁ : ℝ)) * ((C : ℝ) * J₂ + 1) + ω / 4 < α / 100 ∧
      ω + 4 / (J₂ : ℝ) < α / 100 ∧
      24 * ω + 3 * τ + 2 / (J₂ : ℝ) < α / 100 ∧
      2 / (J₁ : ℝ) < α / 100 ∧ 1 / (J₂ : ℝ) < α / 100 := by
  let α₀ := min α 1
  have hα₀ : 0 < α₀ := lt_min hα zero_lt_one
  have hα₀α : α₀ ≤ α := min_le_left _ _
  have hα₀one : α₀ ≤ 1 := min_le_right _ _
  obtain ⟨J₂, hJ₂gt⟩ := exists_nat_gt ((1000000 : ℝ) / α₀)
  have hJ₂pos : (0 : ℝ) < J₂ :=
    (by positivity : (0 : ℝ) < 1000000 / α₀).trans hJ₂gt
  have hJ₂ : 1 ≤ J₂ := Nat.succ_le_iff.mpr (by exact_mod_cast hJ₂pos)
  have hJ₂large := (div_lt_iff₀ hα₀).mp hJ₂gt
  let L₂ : ℝ := (C : ℝ) * J₂ + 1
  have hL₂ : 1 ≤ L₂ := by
    have hp : 0 ≤ (C : ℝ) * J₂ := by positivity
    dsimp only [L₂]
    linarith
  have hL₂pos : 0 < L₂ := zero_lt_one.trans_le hL₂
  obtain ⟨J₁, hJ₁gt⟩ := exists_nat_gt (1000000 * L₂ / α₀)
  have hJ₁pos : (0 : ℝ) < J₁ :=
    (by positivity : (0 : ℝ) < 1000000 * L₂ / α₀).trans hJ₁gt
  have hJ₁ : 1 ≤ J₁ := Nat.succ_le_iff.mpr (by exact_mod_cast hJ₁pos)
  have hJ₁large := (div_lt_iff₀ hα₀).mp hJ₁gt
  have hinv₂ : 1000000 * (J₂ : ℝ)⁻¹ < α₀ := by
    change 1000000 / (J₂ : ℝ) < α₀
    exact (div_lt_iff₀ hJ₂pos).mpr (by nlinarith only [hJ₂large])
  have hinv₁ : 1000000 * L₂ * (J₁ : ℝ)⁻¹ < α₀ := by
    change (1000000 * L₂) / (J₁ : ℝ) < α₀
    exact (div_lt_iff₀ hJ₁pos).mpr (by nlinarith only [hJ₁large])
  have hinv₁small : 1000000 * (J₁ : ℝ)⁻¹ < α₀ := by
    have hp : 0 ≤ (L₂ - 1) * (J₁ : ℝ)⁻¹ :=
      mul_nonneg (sub_nonneg.mpr hL₂) (inv_nonneg.mpr hJ₁pos.le)
    nlinarith only [hinv₁, hp]
  let ω := α₀ * S / (1000000 * L₂ * (S + 1))
  let τ := 4 * ω / S
  have hSone : 0 < S + 1 := by linarith only [hS]
  have hω : 0 < ω := by dsimp only [ω]; positivity
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hωid : 1000000 * L₂ * ω * (S + 1) = α₀ * S := by
    dsimp only [ω]
    field_simp [ne_of_gt hL₂pos, ne_of_gt hSone]
  have hτid : 1000000 * L₂ * τ * (S + 1) = 4 * α₀ := by
    dsimp only [τ, ω]
    field_simp [ne_of_gt hL₂pos, ne_of_gt hSone, ne_of_gt hS]
  have hωL : 1000000 * L₂ * ω < α₀ := by
    apply (mul_lt_mul_iff_left₀ hSone).mp
    rw [hωid]
    nlinarith only [hα₀]
  have hτL : 1000000 * L₂ * τ ≤ 4 * α₀ := by
    apply (mul_le_mul_iff_left₀ hSone).mp
    rw [hτid]
    nlinarith only [mul_nonneg hα₀.le hS.le]
  have hωsmall : 1000000 * ω < α₀ := by
    have hp : 0 ≤ (L₂ - 1) * ω := mul_nonneg (sub_nonneg.mpr hL₂) hω.le
    nlinarith only [hωL, hp]
  have hτsmall : 1000000 * τ ≤ 4 * α₀ := by
    have hp : 0 ≤ (L₂ - 1) * τ := mul_nonneg (sub_nonneg.mpr hL₂) hτ.le
    nlinarith only [hτL, hp]
  refine ⟨J₂, J₁, hJ₂, hJ₁, ω, τ, hω, hτ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hωsmall, hα₀one]
  · nlinarith only [hτsmall, hα₀one]
  · dsimp only [τ]
    exact mul_div_cancel₀ (4 * ω) hS.ne'
  · change (3 * ω + 2 * (J₁ : ℝ)⁻¹) * L₂ + ω / 4 < α / 100
    nlinarith only [hωL, hinv₁, hωsmall, hα₀α, hα₀]
  · change ω + 4 * (J₂ : ℝ)⁻¹ < α / 100
    nlinarith only [hωsmall, hinv₂, hα₀α, hα₀]
  · change 24 * ω + 3 * τ + 2 * (J₂ : ℝ)⁻¹ < α / 100
    nlinarith only [hωsmall, hτsmall, hinv₂, hα₀α, hα₀]
  · change 2 * (J₁ : ℝ)⁻¹ < α / 100
    nlinarith only [hinv₁small, hα₀α, hα₀]
  · rw [one_div]
    nlinarith only [hinv₂, hα₀α, hα₀]

end Submission.Obl.k4_scalar_graph_residual_discovery
