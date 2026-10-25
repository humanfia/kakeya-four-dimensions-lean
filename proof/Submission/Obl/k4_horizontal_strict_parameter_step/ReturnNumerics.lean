import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ReturnNumerics.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- One fixed output loss absorbs every smaller chart loss, uniformly across the
charts and across the physical scales `a,w≤1`. -/
theorem eventually_raw_return_numerics {ε δ : ℝ} (hδ : 0 < δ) (hgap : 5 * δ < ε) :
    ∀ᶠ N : ℝ in atTop, 2 ≤ N ∧ 2 ≤ N ^ ε ∧
      ∀ ξ a w : ℝ, ξ ≤ δ → 0 ≤ a → a ≤ 1 → 0 ≤ w → w ≤ 1 →
        N ^ ξ + 18 * a * (2 * N ^ ξ + N ^ δ + w + 1) ≤ N ^ ε ∧
        N ^ (-ε) + N ^ (-ε) * N ^ (ξ + δ) < N ^ (-(2 * ξ + δ)) := by
  have hδε : δ < ε := by linarith
  have hε : 0 < ε := by linarith
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_const_mul_rpow_le 91 hδε,
    eventually_const_mul_rpow_le 2 (a := (0 : ℝ)) (b := ε) hε,
    eventually_const_mul_rpow_le 4 (a := 2 * δ - ε) (b := -3 * δ) (by linarith)]
    with N hN hnorm htwo hreserve
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hNδ : 1 ≤ N ^ δ := Real.one_le_rpow hN1 hδ.le
  have hpow (r s : ℝ) (h : r ≤ s) : N ^ r ≤ N ^ s :=
    Real.rpow_le_rpow_of_exponent_le hN1 h
  refine ⟨hN, by simpa only [Real.rpow_zero, mul_one] using htwo, ?_⟩
  intro ξ a w hξ ha ha1 hw hw1
  have hξδ : N ^ ξ ≤ N ^ δ := hpow ξ δ hξ
  have hnorm' : N ^ ξ + 18 * a * (2 * N ^ ξ + N ^ δ + w + 1) ≤ 91 * N ^ δ := by
    calc
      _ ≤ N ^ δ + 18 * 1 * (2 * N ^ δ + N ^ δ + 1 + 1) := by gcongr
      _ ≤ _ := by linarith
  refine ⟨hnorm'.trans hnorm, ?_⟩
  have hsum : N ^ (-ε) + N ^ (-ε) * N ^ (ξ + δ) ≤ 2 * N ^ (2 * δ - ε) := by
    have hfirst := hpow (-ε) (2 * δ - ε) (by linarith)
    have hsecond : N ^ (-ε) * N ^ (ξ + δ) ≤ N ^ (2 * δ - ε) := by
      rw [← Real.rpow_add hNp]
      exact hpow _ _ (by linarith)
    linarith
  have hstrict : 2 * N ^ (2 * δ - ε) < N ^ (-3 * δ) := by
    have hp : 0 < N ^ (2 * δ - ε) := Real.rpow_pos_of_pos hNp _
    linarith
  exact hsum.trans_lt (hstrict.trans_le (hpow (-3 * δ) (-(2 * ξ + δ)) (by linarith)))

end Submission.Obl.k4_horizontal_strict_parameter_step
