import Mathlib
import Submission.Obl.k4_scalar_coefficient_clustering.Powers

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open Filter
open scoped Topology

/-- Choose the input loss after the power-small density exception is known.
This order is essential when its exponent is smaller than the requested loss. -/
theorem recovery_parameters (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 ∧ δ ≤ ε / 100 ∧
      ∀ᶠ k in atTop,
        2 * N k ^ (ε / 100) ≤ N k ^ ε ∧
        N k ^ (-ε) + 3 * (N k ^ (-c) + 10 * N k ^ (4 * (ε / 100) - ε / 2)) ≤
          N k ^ (-δ) := by
  let τ := ε / 100
  let δ := min τ (min (c / 100) 1)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδτ : δ ≤ τ := min_le_left _ _
  have hδc : δ ≤ c / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hδε : δ ≤ ε := by dsimp [τ] at hδτ; linarith
  have he1 : δ - ε < 0 := by dsimp [τ] at hδτ; linarith
  have he2 : δ - c < 0 := by linarith
  have he3 : δ + 4 * τ - ε / 2 < 0 := by dsimp [τ] at hδτ ⊢; linarith
  let e := max (δ - ε) (max (δ - c) (δ + 4 * τ - ε / 2))
  have he : e < 0 := max_lt he1 (max_lt he2 he3)
  have hsmall := Submission.Obl.k4_scalar_coefficient_clustering.negative_two_powers_eventually
    (C := 34) he he
  have h2 : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (ε - τ) :=
    (tendsto_rpow_atTop (by dsimp [τ]; linarith : 0 < ε - τ)).eventually (eventually_ge_atTop 2)
  refine ⟨δ, hδ, hδε, hδ1, hδτ, ?_⟩
  filter_upwards [hNt.eventually hsmall, hNt.eventually h2] with k hsmallk h2k
  have hNk : 1 ≤ N k := le_trans (by norm_num) (hN k)
  have hNk0 : 0 < N k := zero_lt_one.trans_le hNk
  have hgap : 2 * N k ^ τ ≤ N k ^ ε := by
    calc
      _ ≤ N k ^ (ε - τ) * N k ^ τ :=
        mul_le_mul_of_nonneg_right h2k (Real.rpow_pos_of_pos hNk0 _).le
      _ = _ := by rw [← Real.rpow_add hNk0]; congr 1; ring
  have hp1 : N k ^ (δ - ε) ≤ N k ^ e :=
    Real.rpow_le_rpow_of_exponent_le hNk (le_max_left _ _)
  have hp2 : N k ^ (δ - c) ≤ N k ^ e :=
    Real.rpow_le_rpow_of_exponent_le hNk ((le_max_left _ _).trans (le_max_right _ _))
  have hp3 : N k ^ (δ + 4 * τ - ε / 2) ≤ N k ^ e :=
    Real.rpow_le_rpow_of_exponent_le hNk ((le_max_right _ _).trans (le_max_right _ _))
  have hnorm : N k ^ (δ - ε) + 3 * N k ^ (δ - c) +
      30 * N k ^ (δ + 4 * τ - ε / 2) ≤ 1 := by
    have hp : 0 ≤ N k ^ e := (Real.rpow_pos_of_pos hNk0 _).le
    linarith
  have hid : N k ^ δ *
      (N k ^ (-ε) + 3 * (N k ^ (-c) + 10 * N k ^ (4 * τ - ε / 2))) =
      N k ^ (δ - ε) + 3 * N k ^ (δ - c) + 30 * N k ^ (δ + 4 * τ - ε / 2) := by
    simp only [sub_eq_add_neg, Real.rpow_add hNk0]
    ring
  have hmass : N k ^ (-ε) + 3 * (N k ^ (-c) + 10 * N k ^ (4 * τ - ε / 2)) ≤ N k ^ (-δ) := by
    rw [Real.rpow_neg hNk0.le δ, ← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNk0 δ)).mpr
    simpa only [mul_comm] using hid.trans_le hnorm
  exact ⟨hgap, hmass⟩

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
