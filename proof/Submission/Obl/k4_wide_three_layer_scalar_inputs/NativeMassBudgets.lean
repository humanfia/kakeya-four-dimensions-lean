import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- The original mass floor survives the deep-state pruning and the
normalized agreement loss. The conditional palette cost fits the field's
input loss, and its capture pays the last residual pruning. -/
theorem eventually_native_mass_budgets {σ ζ β η ε : ℝ}
    (hprune : σ < ζ) (hcond : σ + ζ < η) (hag : 10 * σ + ζ < β)
    (hmass : σ < η) (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop, ∀ K H : ℝ,
      0 ≤ K → 0 ≤ H → K ≤ N ^ σ → H ≤ N ^ σ →
      81 * N ^ (-ζ) ≤ N ^ (-σ) / 8 ∧
      2 * (K * N ^ ζ) * N ^ (-β) * (100000000 * K ^ 4 * H ^ 4) ≤ N ^ (-σ) / 8 ∧
      2 * (K * N ^ ζ) ≤ N ^ η ∧
      4 * N ^ (-η) ≤ N ^ (-σ) ∧ 54 ≤ N ^ ε := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_rpow_le 648 (a := -ζ) (b := -σ) (by linarith),
    eventually_const_mul_rpow_le 1600000000 (a := 9 * σ + ζ - β) (b := -σ) (by linarith),
    eventually_const_mul_rpow_le 2 hcond,
    eventually_const_mul_rpow_le 4 (a := -η) (b := -σ) (by linarith),
    eventually_const_mul_rpow_le 54 (a := 0) hε]
    with N hN hpr hagree hstate hfloor h54
  have hNp : 0 < N := zero_lt_one.trans_le hN
  simp only [Real.rpow_zero, mul_one] at h54
  intro K H hK hH hKN hHN
  have hstate' : 2 * (K * N ^ ζ) ≤ N ^ η := by
    calc _ ≤ 2 * (N ^ σ * N ^ ζ) := by gcongr
      _ = 2 * N ^ (σ + ζ) := by rw [← Real.rpow_add hNp]
      _ ≤ _ := hstate
  have hpower : (N ^ σ) ^ 4 * (N ^ σ) ^ 4 * N ^ σ * N ^ ζ * N ^ (-β) =
      N ^ (9 * σ + ζ - β) := by
    rw [← Real.rpow_mul_natCast hNp.le,
      ← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_add hNp,
      ← Real.rpow_add hNp]
    congr 1
    ring
  have hagree' : 2 * (K * N ^ ζ) * N ^ (-β) * (100000000 * K ^ 4 * H ^ 4) ≤ N ^ (-σ) / 8 := by
    calc _ = 200000000 * (K ^ 4 * H ^ 4 * K * N ^ ζ * N ^ (-β)) := by ring
      _ ≤ 200000000 * ((N ^ σ) ^ 4 * (N ^ σ) ^ 4 * N ^ σ * N ^ ζ * N ^ (-β)) := by gcongr
      _ = 200000000 * N ^ (9 * σ + ζ - β) := by rw [hpower]
      _ ≤ N ^ (-σ) / 8 := by linarith
  exact ⟨by linarith, hagree', hstate', hfloor, h54⟩

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
