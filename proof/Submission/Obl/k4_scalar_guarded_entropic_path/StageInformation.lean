import Submission.Obl.k4_scalar_guarded_entropic_path.StageLayout
import Submission.Obl.k4_scalar_guarded_entropic_path.WindowBudget

/-! The actual finite layout pays for the master velocity record and
the constant velocity and point ambiguities before choosing a window. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.StageLayout

open Filter
open scoped Topology

noncomputable section

variable {k : ℕ} {R δ κ η : ℝ} (q : StageLayout k R δ κ η)

theorem master_entropy_fraction :
    2 * (q.C : ℝ) * ((q.m : ℝ) + 4) / (q.L : ℝ) ≤ δ / 2 := by
  have hL : (0 : ℝ) < q.L := by exact_mod_cast q.L_pos
  have hf := (div_le_iff₀ hL).mp q.entropy_fraction
  have hc : 0 ≤ (q.C : ℝ) * ((q.m : ℝ) + 4) :=
    mul_nonneg (Nat.cast_nonneg _) (by positivity)
  apply (div_le_iff₀ hL).mpr
  nlinarith only [hf, hc]

/-- A single cutoff works for every master record count satisfying its
logarithmic bound. The master partition may be chosen at the late sample. -/
theorem eventually_window_cost (N : ℕ → ℝ) (hNt : Tendsto N atTop atTop) :
    ∀ᶠ j in atTop, ∀ M : ℕ,
      Real.log (M : ℝ) ≤ ((q.m : ℝ) + 4) * Real.log (N j) →
      Info.informationExponent (N j)
        (Info.windowCost q.L q.C M 4 (4 ^ (3 * (q.m ^ 2 + 1)))) ≤ δ := by
  have hδ : 0 < δ := q.scale_pos.trans_le q.scale_error
  let T := 2 * (Real.log (4 : ℝ) +
    Real.log ((4 ^ (3 * (q.m ^ 2 + 1)) : ℕ) : ℝ) + 4) + 1
  filter_upwards [hNt.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp hNt).eventually_ge_atTop (T / (δ / 2))]
    with j hNj hT M hM
  apply Info.window_informationExponent_le hNj q.L_pos hM q.master_entropy_fraction
  have ht := (div_le_iff₀ (half_pos hδ)).mp hT
  simpa only [T, Function.comp_apply, mul_comm, Nat.cast_ofNat] using ht

/-- With the actual fixed ambiguity counts, the information exponent is
positive, has room for a factor two, and is at most the stage error on
one original inner tail. The later window choice uses this SAME exponent. -/
theorem eventually_window_alpha (N : ℕ → ℝ) (Sv : ℕ → Finset ℤ)
    (hNt : Tendsto N atTop atTop)
    (hmaster : ∀ᶠ j in atTop,
      ((max (Sv j).card 1 : ℕ) : ℝ) ≤ N j ^ ((q.m : ℝ) + 4)) :
    ∀ᶠ j in atTop,
      let α := Info.informationExponent (N j)
        (Info.windowCost q.L q.C (max (Sv j).card 1) 4 (4 ^ (3 * (q.m ^ 2 + 1))))
      0 < α ∧ 2 ≤ N j ^ α ∧ α ≤ δ := by
  have hlog : ∀ᶠ j in atTop,
      Real.log ((max (Sv j).card 1 : ℕ) : ℝ) ≤
        ((q.m : ℝ) + 4) * Real.log (N j) := by
    filter_upwards [hNt.eventually_gt_atTop 0, hmaster] with j hNj hMj
    have hpos : (0 : ℝ) < (max (Sv j).card 1 : ℕ) := by
      exact_mod_cast (zero_lt_one.trans_le (le_max_right (Sv j).card 1))
    exact (Real.log_le_log hpos hMj).trans_eq (Real.log_rpow hNj _)
  filter_upwards [hNt.eventually_ge_atTop 2, q.eventually_window_cost N hNt, hlog]
    with j hNj hj hMj
  have hcost : 0 ≤ Info.windowCost q.L q.C (max (Sv j).card 1) 4
      (4 ^ (3 * (q.m ^ 2 + 1))) :=
    Info.windowCost_nonneg (le_max_right _ _) (by norm_num)
      (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 4))
  have hs := Info.informationExponent_spec hNj hcost
  exact ⟨hs.1, hs.2.1, hj _ hMj⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.StageLayout
