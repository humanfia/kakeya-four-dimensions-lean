import Mathlib

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-!
Slow diagonal choices for the fixed-tolerance convention in the supplied
paper. Each estimate is first used at a fixed finite accuracy; only then
does the number of estimates increase and the accuracy tend to zero.
-/

namespace Submission.Lib.K4ModelReduction

open Filter

/-- Countably many eventual requirements can be imposed on a monotonically
growing finite initial list. The list can be chosen to grow at most as fast
as the index itself. -/
theorem exists_slow_diagonal (P : ℕ → ℕ → Prop)
    (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ k : ℕ → ℕ, Monotone k ∧ Tendsto k atTop atTop ∧
      (∀ n, k n ≤ n) ∧ ∀ᶠ n in atTop, ∀ j ≤ k n, P j n := by
  classical
  have hfinite (m : ℕ) : ∀ᶠ n in atTop, ∀ j ≤ m, P j n := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using
      (Finset.eventually_all (Finset.range (m + 1))).2 (fun j _ => hP j)
  choose T hT using fun m => eventually_atTop.1 (hfinite m)
  let k : ℕ → ℕ := fun n => Nat.findGreatest (fun m => T m ≤ n) n
  refine ⟨k, ?_, ?_, fun n => Nat.findGreatest_le n, ?_⟩
  · intro a b hab
    exact Nat.findGreatest_mono (fun _ hm => hm.trans hab) hab
  · refine tendsto_atTop.2 fun m => ?_
    filter_upwards [eventually_ge_atTop (max m (T m))] with n hn
    exact Nat.le_findGreatest ((le_max_left _ _).trans hn)
      ((le_max_right _ _).trans hn)
  · filter_upwards [eventually_ge_atTop (T 0)] with n hn
    exact hT (k n) n (Nat.findGreatest_spec (P := fun m => T m ≤ n) (Nat.zero_le n) hn)

/-- A slowly vanishing positive tolerance can be chosen together with a
slowly growing finite list, without interchanging the two limits. -/
theorem exists_slow_tolerance (P : ℕ → ℝ → ℕ → Prop)
    (hP : ∀ m, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, P m ε n) :
    ∃ (k : ℕ → ℕ) (ε : ℕ → ℝ),
      Monotone k ∧ Tendsto k atTop atTop ∧
      (∀ n, 0 < ε n) ∧ Antitone ε ∧ Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ n in atTop, ∀ j ≤ k n, P j (ε n) n := by
  classical
  let Q : ℕ → ℕ → Prop := fun m n =>
    ∀ j ≤ m, P j (1 / ((m : ℝ) + 1)) n
  have hQ (m : ℕ) : ∀ᶠ n in atTop, Q m n := by
    simpa only [Q, Finset.mem_range, Nat.lt_succ_iff] using
      (Finset.eventually_all (Finset.range (m + 1))).2
        (fun j _ => hP j (1 / ((m : ℝ) + 1)) (by positivity))
  obtain ⟨k, hkmono, hk, _, hgood⟩ := exists_slow_diagonal Q hQ
  refine ⟨k, (fun n => 1 / ((k n : ℝ) + 1)), hkmono, hk, ?_, ?_, ?_, ?_⟩
  · intro n
    positivity
  · intro a b hab
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right (hkmono hab) 1)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  · filter_upwards [hgood] with n hn
    exact hn (k n) le_rfl

end Submission.Lib.K4ModelReduction
