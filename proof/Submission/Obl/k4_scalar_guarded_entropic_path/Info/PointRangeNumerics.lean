import Submission.Obl.k4_scalar_guarded_entropic_path.Info.CanonicalPointRanges
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

/-! Original-unit block counts and a strict exponent margin give the
precise quantitative inputs to the constant-cost point-state theorem. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Filter
open PathGeometry

noncomputable section

/-- The SAME allowance in both calibrated block counts only costs twice
its exponent in the actual duration ratio. -/
theorem duration_ratio_of_calibrated_counts {N B κ rc rf v R : ℝ} {Tc Tf : ℕ}
    (hN : 1 ≤ N) (hB : 0 < B) (hBv : B ≤ N ^ v)
    (hcoarse : (2 : ℝ) ^ Tc ≤ B * N ^ (κ * rc))
    (hfine : N ^ (κ * rf) / B ≤ (2 : ℝ) ^ Tf)
    (hgap : R ≤ κ * (rf - rc) - 2 * v) :
    (((2 : ℝ) ^ Tf)⁻¹) / (((2 : ℝ) ^ Tc)⁻¹) ≤ N ^ (-R) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  apply GeometryPointStates.duration_ratio_le_rpow hN
    (a := v + κ * rc) (b := κ * rf - v)
  · apply hcoarse.trans
    calc
      B * N ^ (κ * rc) ≤ N ^ v * N ^ (κ * rc) :=
        mul_le_mul_of_nonneg_right hBv (Real.rpow_nonneg hN0.le _)
      _ = _ := (Real.rpow_add hN0 _ _).symm
  · apply le_trans _ hfine
    rw [Real.rpow_sub hN0]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) hB hBv
  · linarith

/-- A single strict loss exponent absorbs the explicit graph constant
and its twenty-sixth power, on the original inner tail. -/
theorem eventually_point_range_margin {N : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    {γ scale : ℝ} (hgap : 26 * γ < scale) :
    ∀ᶠ k in atTop, ∀ K : ℝ, 0 ≤ K → K ≤ N k ^ γ →
      47589120000003 * K ^ 26 ≤ N k ^ scale := by
  have hgap' : γ * (26 : ℕ) < scale := by norm_num; linarith
  filter_upwards [hNt.eventually
    (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
      47589120000003 hgap')] with k hk
  intro K hK hKγ
  apply le_trans _ hk
  rw [Real.rpow_mul_natCast (zero_le_one.trans (hN k))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK hKγ 26) (by norm_num)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
