import Mathlib

/-!
# Passing from vanishing losses to a fixed input power

The diagonal below is the final quantifier conversion in Lemma 3.3.  It makes
no monotonicity assumption on the predicate describing a bad configuration.
-/

namespace Submission.Obl.k4_two_color_matching

open Filter

/-- A canonical sequence of positive loss exponents tending to zero. -/
noncomputable def lossExponent (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

lemma lossExponent_pos (k : ℕ) : 0 < lossExponent k := by
  unfold lossExponent
  positivity

lemma lossExponent_tendsto : Tendsto lossExponent atTop (nhds 0) := by
  unfold lossExponent
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0))

/-- Failure of every fixed-loss eventual assertion gives a counterexample at
scale at least `k+2` for each canonical loss exponent. -/
lemma counterexample_sequence_of_no_uniform (Bad : ℝ → ℝ → Prop)
    (h : ¬ ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ¬ Bad η N) :
    ∃ N : ℕ → ℝ, ∀ k : ℕ, (k : ℝ) + 2 ≤ N k ∧ Bad (lossExponent k) (N k) := by
  classical
  have heach : ∀ k : ℕ, ∃ N : ℝ, (k : ℝ) + 2 ≤ N ∧ Bad (lossExponent k) N := by
    intro k
    by_contra hk
    push Not at hk
    apply h
    refine ⟨lossExponent k, lossExponent_pos k, (k : ℝ) + 2,
      by linarith [Nat.cast_nonneg (α := ℝ) k], ?_⟩
    exact hk
  exact Classical.axiomOfChoice heach

lemma uniform_of_no_counterexample_sequence (Bad : ℝ → ℝ → Prop)
    (h : ¬ ∃ N : ℕ → ℝ, ∀ k : ℕ,
      (k : ℝ) + 2 ≤ N k ∧ Bad (lossExponent k) (N k)) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ¬ Bad η N := by
  by_contra hn
  exact h (counterexample_sequence_of_no_uniform Bad hn)

lemma scale_tendsto_of_nat_lower_bound {N : ℕ → ℝ}
    (hN : ∀ k : ℕ, (k : ℝ) + 2 ≤ N k) : Tendsto N atTop atTop := by
  apply tendsto_atTop_mono (fun k : ℕ => le_trans (by linarith : (k : ℝ) ≤ (k : ℝ) + 2) (hN k))
  exact tendsto_natCast_atTop_atTop

/-- A predicate holds eventually at some fixed positive tolerance exactly when
there is no counterexample sequence with the canonical vanishing tolerances. -/
theorem uniform_iff_no_counterexample_sequence (Bad : ℝ → ℝ → Prop)
    (hmono : ∀ η ε N : ℝ, 0 < η → η ≤ ε → Bad η N → Bad ε N) :
    (∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ¬ Bad η N) ↔
    ¬ ∃ N : ℕ → ℝ, ∀ k : ℕ, (k : ℝ) + 2 ≤ N k ∧ Bad (lossExponent k) (N k) := by
  refine ⟨?_, uniform_of_no_counterexample_sequence Bad⟩
  rintro ⟨η, hη, N₀, hN₀, hgood⟩ ⟨N, hN⟩
  have hsmall : ∀ᶠ k : ℕ in atTop, lossExponent k ≤ η :=
    (lossExponent_tendsto.eventually (gt_mem_nhds hη)).mono fun k hk => hk.le
  have hlarge : ∀ᶠ k : ℕ in atTop, N₀ ≤ N k :=
    (scale_tendsto_of_nat_lower_bound fun k => (hN k).1).eventually (eventually_ge_atTop N₀)
  obtain ⟨k, hk, hk'⟩ := (hsmall.and hlarge).exists
  exact hgood (N k) hk' (hmono _ _ _ (lossExponent_pos k) hk (hN k).2)

end Submission.Obl.k4_two_color_matching
