import Submission.Obl.k4_matching_abstract_switching_mixture.Estimates

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open Finset
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite
open Classical

set_option linter.unusedSectionVars false

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- A good start can be selected before its control strategy and target cover:
the averaged failure depends only on the original record and arm laws. -/
theorem exists_start_of_small_kills
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (hP1 : ∑ e, X.P e = 1) (π : Bool → Ar → ℝ) (lam ε : ℝ)
    (hε : 0 ≤ ε) (m : ℕ)
    (hbad : ∑ e, X.P e * (if X.good e then (0 : ℝ) else 1) ≤ ε)
    (hlight : ∀ c, ∑ e, X.P e * (if X.heavy π lam e c then (0 : ℝ) else 1) ≤ ε)
    (hbudget : ((2 : ℝ) ^ (m + 1) - 1) * (4 * ε) ≤ 1 / 2) :
    ∃ a, 0 < X.P a ∧ X.failBound π lam ε (m + 1) a ≤ 1 / 2 := by
  have hbadall : ∑ e, X.P e * ((if X.good e then (0 : ℝ) else 1) +
      ∑ c : Bool, (if X.heavy π lam e c then (0 : ℝ) else 1)) + ε ≤ 4 * ε := by
    have hsplit : ∑ e, X.P e * ((if X.good e then (0 : ℝ) else 1) +
        ∑ c : Bool, (if X.heavy π lam e c then (0 : ℝ) else 1)) =
        (∑ e, X.P e * (if X.good e then (0 : ℝ) else 1)) +
        ∑ c : Bool, ∑ e, X.P e * (if X.heavy π lam e c then (0 : ℝ) else 1) := by
      simp only [mul_add, sum_add_distrib, mul_sum]
      rw [sum_comm]
    rw [hsplit, Fintype.sum_bool]
    linarith [hlight true, hlight false]
  have havg := X.sum_mul_failBound_le hP hP1 π lam hε (m + 1) X.P 1
    zero_le_one hP (fun e => by simp)
  simp only [one_mul] at havg
  have hnonneg : 0 ≤ (2 : ℝ) ^ (m + 1) - 1 := by
    have h := one_le_pow₀ (n := m + 1) (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hsum : ∑ a, X.P a * X.failBound π lam ε (m + 1) a ≤ 1 / 2 :=
    havg.trans ((mul_le_mul_of_nonneg_left hbadall hnonneg).trans hbudget)
  exact exists_pos_weight_le X.P _ hP hP1 hsum

end Submission.Obl.k4_matching_abstract_switching_mixture
