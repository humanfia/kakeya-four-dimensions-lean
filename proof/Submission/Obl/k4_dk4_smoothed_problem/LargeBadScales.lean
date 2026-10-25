import Submission.Obl.k4_dk4_smoothed_problem.BadScales
import Submission.Obl.k4_dk4_smoothed_problem.DyadicNumerics

open Filter

namespace Submission.Obl.k4_dk4_smoothed_problem

theorem exists_large_bad_sequence
    (h : ¬ Submission.Lib.KakeyaCovering.DiscreteKakeyaEstimate) :
    ∃ σ c R : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < c ∧ 1 ≤ R ∧
      ∃ κ : ℕ → ℕ, (∀ j, 1 ≤ κ j ∧ j ≤ κ j) ∧
        (∀ j, 2 ≤ scale (κ j) ∧ c + 1 ≤ scale (κ j) ∧ R + 3 ≤ scale (κ j)) ∧
        ∀ j, Nonempty (BadConfiguration c R σ (κ j)) := by
  classical
  obtain ⟨σ, c, R, hσ, hσ1, hc, hR, hbad⟩ := exists_bad_configuration h
  have ht : Tendsto (fun a : ℕ => (2 : ℝ) ^ a) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨a, ha⟩ := (ht.eventually_ge_atTop (max (c + 1) (R + 3))).exists
  choose κ hκ hconfig using fun j => hbad (max (max a 1) j)
  have hκ1 (j : ℕ) : 1 ≤ κ j :=
    (le_max_right a 1).trans ((le_max_left (max a 1) j).trans (hκ j))
  have hκj (j : ℕ) : j ≤ κ j := (le_max_right (max a 1) j).trans (hκ j)
  refine ⟨σ, c, R, hσ, hσ1, hc, hR, κ, fun j => ⟨hκ1 j, hκj j⟩, ?_, hconfig⟩
  intro j
  have hak : a ≤ κ j :=
    (le_max_left a 1).trans ((le_max_left (max a 1) j).trans (hκ j))
  have hpow : (2 : ℝ) ^ a ≤ scale (κ j) :=
    pow_le_pow_right₀ (by norm_num) hak
  have htwo : (2 : ℝ) ≤ scale (κ j) := by
    simpa only [pow_one, scale] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hκ1 j)
  exact ⟨htwo, ((le_max_left _ _).trans ha).trans hpow,
    ((le_max_right _ _).trans ha).trans hpow⟩

end Submission.Obl.k4_dk4_smoothed_problem
