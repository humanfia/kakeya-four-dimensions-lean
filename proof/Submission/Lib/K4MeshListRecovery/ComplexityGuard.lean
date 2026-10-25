/-
Adapted from: here:o064
Original proofs by session x0217 in this workspace. Uses the accepted
K4OriginalLists and K4ModelReduction APIs for paper Lemma a03:actual-lists.
-/

import Mathlib

/-!
The original-resolution complexity guard from the supplied paper, Section 4.
A fixed scenario's polynomial complexity is absorbed uniformly in the old
complexity exponent; the scenario may be chosen after the tangent diagonal.
-/

namespace Submission.Lib.K4MeshListRecovery

open Filter

/-- The guard eventually dominates every fixed polynomial, uniformly in the old bound. -/
theorem eventually_polynomial_le_complexity_guard (C : ℝ) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ,
      C * (1 + (M : ℝ)) ^ d ≤ (2 : ℝ) ^ ((M + n) ^ 2) := by
  obtain ⟨c, hc⟩ := exists_nat_gt C
  have hc' : C ≤ (2 : ℝ) ^ c := by
    have hcpow : (c : ℝ) < (2 : ℝ) ^ c := by exact_mod_cast c.lt_two_pow_self
    exact (hc.trans hcpow).le
  refine eventually_atTop.mpr ⟨max c d + 1, ?_⟩
  intro n hn M
  have hnc : c ≤ n := by omega
  have hnd : d ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn2 : n ≤ n * n := by nlinarith
  have hMd : M * d ≤ M * n := Nat.mul_le_mul_left M hnd
  have hexp : c + M * d ≤ (M + n) ^ 2 := by nlinarith
  have hbase : 1 + (M : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast (show 1 + M ≤ 2 ^ M by
      simpa only [add_comm] using Nat.succ_le_of_lt M.lt_two_pow_self)
  calc
    _ ≤ (2 : ℝ) ^ c * (1 + (M : ℝ)) ^ d :=
      mul_le_mul_of_nonneg_right hc' (by positivity)
    _ ≤ (2 : ℝ) ^ c * ((2 : ℝ) ^ M) ^ d := by gcongr
    _ = (2 : ℝ) ^ (c + M * d) := by rw [pow_add, pow_mul]
    _ ≤ (2 : ℝ) ^ ((M + n) ^ 2) := by gcongr <;> norm_num

/-- A scenario-dependent polynomial bound fits a guard fixed before the sample is chosen. -/
theorem eventually_scenario_le_complexity_guard (P : ℕ → ℝ)
    (hP : ∃ C : ℝ, ∃ d : ℕ, ∀ M, P M ≤ C * (1 + (M : ℝ)) ^ d) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ, P M ≤ (2 : ℝ) ^ ((M + n) ^ 2) := by
  obtain ⟨C, d, hP⟩ := hP
  filter_upwards [eventually_polynomial_le_complexity_guard C d] with n hn M
  exact (hP M).trans (hn M)

end Submission.Lib.K4MeshListRecovery
