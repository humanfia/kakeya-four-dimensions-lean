/- Adapted from this LOT tree o218, branch x0760, commit 5db19453bd17cc371d54c5ac350db64cdc0ec595,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/ChartReplacement.lean. Original attribution, when present, is preserved below. -/

import Mathlib

/-! The frame is the one described in this LOT tree, o274/x0969's16:12 post
and commit c6776fd2432c9c61c32e60acb489ef2058ab217b, Inherited/Native/Keys.lean.
The formulas and proofs below are written here; no unaccepted module is imported.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

/-- Linear transverse coefficient of a physical quadratic minus a native affine
field, in the frame Y=c2+t*c3+c4*Z+m*U, divided by hidden accuracy a. -/
noncomputable def transverseLinear (G : Fin 6 → ℝ) (c : Fin 5 → ℝ)
    (nativeSlope a m t Z : ℝ) : ℝ :=
  (m / a) * (G 2 + G 4 * t + 2 * G 5 * (c 2 + t * c 3 + c 4 * Z) - nativeSlope)

/-- The native affine slope and every lower quadratic term cancel exactly
when the intercept is moved onto its actual chart motion. -/
theorem transverseLinear_sub (G : Fin 6 → ℝ) (c : Fin 5 → ℝ)
    (nativeSlope a m t Z Z' : ℝ) :
    transverseLinear G c nativeSlope a m t Z - transverseLinear G c nativeSlope a m t Z' =
      (2 * m * G 5 * c 4 / a) * (Z - Z') := by
  simp only [transverseLinear, div_eq_mul_inv]
  ring

/-- Chart replacement only costs the physical Y-squared coefficient and the
original intercept error. It does not cost a new coefficient norm or raw R. -/
theorem transverseLinear_chart_error (G : Fin 6 → ℝ) (c : Fin 5 → ℝ)
    {nativeSlope a m t Z Z' B C δ : ℝ} (ha : 0 < a) (hm : 0 ≤ m)
    (hB : |G 5| ≤ B) (hC : |c 4| ≤ C) (hδ : |Z - Z'| ≤ δ) :
    |transverseLinear G c nativeSlope a m t Z -
      transverseLinear G c nativeSlope a m t Z'| ≤ 2 * (m / a) * B * C * δ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hC
  calc
    _ = 2 * (m / a) * |G 5| * |c 4| * |Z - Z'| := by
      rw [transverseLinear_sub]
      simp only [abs_mul, abs_div, abs_of_pos ha, abs_of_nonneg hm,
        show |(2 : ℝ)| = 2 by norm_num]
      ring
    _ ≤ _ := by gcongr

/-- Fixed-power mesh margin for physical chart replacement. -/
theorem transverseLinear_chart_error_power (G : Fin 6 → ℝ) (c : Fin 5 → ℝ)
    {N sp B C slack M nativeSlope m t Z Z' : ℝ}
    (hN : 1 ≤ N) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hB : |G 5| ≤ N ^ B) (hC : |c 4| ≤ N ^ C)
    (hZ : |Z - Z'| ≤ 2 * N ^ (-M))
    (hconst : 4 ≤ N ^ slack) (hgap : sp + B + C + slack ≤ M / 2) :
    |transverseLinear G c nativeSlope (N ^ (-sp)) m t Z -
      transverseLinear G c nativeSlope (N ^ (-sp)) m t Z'| ≤ N ^ (-M / 2) := by
  have hN0 : 0 < N := by linarith
  have ha : 0 < N ^ (-sp) := Real.rpow_pos_of_pos hN0 _
  have hi : 1 / N ^ (-sp) = N ^ sp := by
    rw [one_div, ← Real.rpow_neg hN0.le, neg_neg]
  calc
    _ ≤ 2 * (m / N ^ (-sp)) * N ^ B * N ^ C * (2 * N ^ (-M)) :=
      transverseLinear_chart_error G c ha hm hB hC hZ
    _ ≤ 2 * (1 / N ^ (-sp)) * N ^ B * N ^ C * (2 * N ^ (-M)) := by gcongr
    _ = 4 * N ^ (sp + B + C - M) := by
      rw [hi]
      calc
        _ = 4 * ((N ^ sp * N ^ B) * N ^ C * N ^ (-M)) := by ring
        _ = _ := by rw [← Real.rpow_add hN0, ← Real.rpow_add hN0,
          ← Real.rpow_add hN0, sub_eq_add_neg]
    _ ≤ N ^ slack * N ^ (sp + B + C - M) := by gcongr
    _ = N ^ (slack + (sp + B + C - M)) := (Real.rpow_add hN0 _ _).symm
    _ ≤ N ^ (-M / 2) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The actual wide-return horizons pay the transport error uniformly over
all coefficient losses at most s0, using the calibrated physical bound
N^(4*kappa*s0+eta). Every remaining input is the actual chart data. -/
theorem eventually_transverse_chart_replacement
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Filter.Tendsto N Filter.atTop Filter.atTop)
    {s₀ sp κ M : ℝ} (hs₀ : 0 < s₀) (hsp : sp < 3 * s₀ / 2)
    (hκ : κ ≤ 1) (hM : 100 * s₀ < M) :
    ∀ᶠ k in Filter.atTop, ∀ (η : ℝ), η ≤ s₀ →
      ∀ (G : Fin 6 → ℝ) (c : Fin 5 → ℝ) (nativeSlope m t Z Z' : ℝ),
      0 ≤ m → m ≤ 1 →
      |G 5| ≤ N k ^ (4 * κ * s₀ + η) → |c 4| ≤ N k ^ η →
      |Z - Z'| ≤ 2 * N k ^ (-M) →
      |transverseLinear G c nativeSlope (N k ^ (-sp)) m t Z -
        transverseLinear G c nativeSlope (N k ^ (-sp)) m t Z'| ≤ N k ^ (-M / 2) := by
  have hpow := (tendsto_rpow_atTop hs₀).comp hNt
  filter_upwards [hpow.eventually (Filter.eventually_ge_atTop (4 : ℝ))] with k hk
  intro η hη G c nativeSlope m t Z Z' hm hm1 hG hc hZ
  apply transverseLinear_chart_error_power G c (slack := s₀)
    (by linarith [hN k]) hm hm1 hG hc hZ hk
  have hrate : κ * s₀ ≤ s₀ := by nlinarith
  linarith

end Submission.Obl.k4_wide_three_layer_scalar_inputs
