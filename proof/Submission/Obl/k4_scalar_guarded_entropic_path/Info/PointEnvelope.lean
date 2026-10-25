import Submission.Obl.k4_scalar_guarded_entropic_path.Info.PointRangeNumerics

/-! A common small graph envelope can be chosen after the tangent scale
and before the inner sample. It accommodates both the guard allowance
and the independently chosen density-test tolerance. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Filter

noncomputable section

structure PointEnvelope (N K scale v ε u γ τ : ℝ) : Prop where
  one : 1 ≤ K
  original : N ^ v ≤ K
  fit : N ^ ε ≤ K
  floor : N ^ γ ≤ K
  width : 2 * N ^ (ε + u) ≤ K
  pure : N ^ τ ≤ K
  margin : 47589120000003 * K ^ 26 ≤ N ^ scale

/-- The graph envelope has a fixed tangent exponent 1/1000, even if
the finite guard forces its own allowance exponent to be much smaller. -/
theorem eventually_pointEnvelope {N : ℕ → ℝ}
    (hN : ∀ j, 1 ≤ N j) (hNt : Tendsto N atTop atTop)
    {scale v ε u γ τ : ℝ} (hscale : 0 < scale) (hv : 0 < v)
    (hvscale : v < scale / 100000) (hε : ε ≤ v / 100)
    (hγ : γ ≤ v / 100) (hwidth : ε + u < v) (hτ : τ ≤ scale / 100000) :
    ∀ᶠ j in atTop, PointEnvelope (N j) (N j ^ (scale / 1000)) scale v ε u γ τ := by
  have hvG : v < scale / 1000 := by linarith
  have hεG : ε ≤ scale / 1000 := by linarith
  have hγG : γ ≤ scale / 1000 := by linarith
  have hτG : τ ≤ scale / 1000 := by linarith
  have hwG : ε + u < scale / 1000 := hwidth.trans hvG
  have hmG : 26 * (scale / 1000) < scale := by linarith
  filter_upwards [hNt.eventually
      (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 2 hwG),
    eventually_point_range_margin hN hNt hmG] with j hw hm
  have hN0 : 0 < N j := zero_lt_one.trans_le (hN j)
  exact
    { one := Real.one_le_rpow (hN j) (by linarith)
      original := Real.rpow_le_rpow_of_exponent_le (hN j) hvG.le
      fit := Real.rpow_le_rpow_of_exponent_le (hN j) hεG
      floor := Real.rpow_le_rpow_of_exponent_le (hN j) hγG
      width := hw
      pure := Real.rpow_le_rpow_of_exponent_le (hN j) hτG
      margin := hm _ (Real.rpow_nonneg hN0.le _) le_rfl }

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
