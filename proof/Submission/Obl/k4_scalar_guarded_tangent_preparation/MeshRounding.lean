import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Filter
open scoped Topology

/-- The finite depth grid below m contains a predecessor for each real
depth in [0,m], losing less than one mesh step. -/
theorem exists_grid_depth_below {m : ℕ} (hm : 1 ≤ m) {r : ℝ}
    (hr : 0 ≤ r) (hrm : r ≤ (m : ℝ)) :
    ∃ j : Fin (m ^ 2 + 1), (j : ℝ) / (m : ℝ) ≤ r ∧
      r < (j : ℝ) / (m : ℝ) + 1 / (m : ℝ) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  let j := ⌊(m : ℝ) * r⌋₊
  have hle : (j : ℝ) ≤ (m : ℝ) * r := Nat.floor_le (mul_nonneg hm0.le hr)
  have hlt : (m : ℝ) * r < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hj : j ≤ m ^ 2 := by
    have h : (j : ℝ) ≤ (m : ℝ) ^ 2 := hle.trans (by nlinarith)
    exact_mod_cast h
  refine ⟨⟨j, Nat.lt_succ_of_le hj⟩, (div_le_iff₀ hm0).2 (by nlinarith), ?_⟩
  rw [← add_div, lt_div_iff₀ hm0]
  simpa only [mul_comm] using hlt

/-- The rectangular exponent changes by at most 3/m when both depths
are rounded down and the scalar profile slope lies in [0,1]. -/
theorem rounded_rectangle_rpow {N d r s r₀ s₀ h : ℝ}
    (hN : 1 ≤ N) (hd : 0 ≤ d) (hd1 : d ≤ 1) (hh : 0 ≤ h)
    (hr : r - r₀ ≤ h) (hs : s - s₀ ≤ h) :
    N ^ (-2 * r₀ - d * s₀) ≤ N ^ (3 * h) * N ^ (-2 * r - d * s) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  rw [← Real.rpow_add hN0]
  apply Real.rpow_le_rpow_of_exponent_le hN
  have hds := mul_le_mul_of_nonneg_left hs hd
  have hdh := mul_le_mul_of_nonneg_right hd1 hh
  nlinarith

/-- The fixed finest velocity mesh is negligible throughout any compact
range of coarser exponent depths. -/
theorem fine_velocity_width {N m b : ℝ} (hN : 2 ≤ N) (hmb : b + 1 ≤ m) :
    2 * N ^ (-m) ≤ N ^ (-b) := by
  have hN0 : 0 < N := by linarith
  calc
    _ ≤ N * N ^ (-m) := mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = N ^ (1 - m) := by rw [sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- A vanishing exponent is subpower in any scale at least one. -/
theorem vanishing_exponent_subpower {N η : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hη : Tendsto η atTop (𝓝 0)) :
    Submission.Obl.k4_discrete_of_terminal_charts.SubpowerBound N (fun k => N k ^ η k) := by
  intro ε hε
  filter_upwards [hη.eventually (gt_mem_nhds hε)] with k hk
  exact Real.rpow_le_rpow_of_exponent_le (hN k) hk.le

/-- All finite-grid losses are paid by one explicit subpower cap. -/
theorem rectangular_slack_subpower {N B α m : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hB : ∀ k, 0 ≤ B k)
    (hBsub : Submission.Obl.k4_discrete_of_terminal_charts.SubpowerBound N B)
    (hα : Tendsto α atTop (𝓝 0)) (hm : Tendsto m atTop atTop) :
    Submission.Obl.k4_discrete_of_terminal_charts.SubpowerBound N
      (fun k => 108 * B k * N k ^ (α k + 3 / m k)) := by
  have hη : Tendsto (fun k => α k + 3 / m k) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, zero_add, mul_zero] using
      hα.add (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hm) :
        Tendsto (fun k => 3 * (m k)⁻¹) atTop (𝓝 (3 * 0)))
  have hpow := vanishing_exponent_subpower hN hη
  have hNB : ∀ k, 0 < N k := fun k => lt_of_lt_of_le zero_lt_one (hN k)
  have hconst := Submission.Obl.k4_discrete_of_terminal_charts.subpower_const hNt (108 : ℝ)
  have hfirst := Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNB
    (fun _ => by norm_num) hB hconst hBsub
  exact Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNB
    (fun k => mul_nonneg (by norm_num) (hB k))
    (fun k => Real.rpow_nonneg (hNB k).le _) hfirst hpow

end Submission.Obl.k4_scalar_guarded_tangent_preparation
