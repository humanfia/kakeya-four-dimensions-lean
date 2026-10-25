import Mathlib

namespace Submission.Obl.k4_matching_refinement_exponent

/-- Only numerical summation remains after the four child interfaces. -/
theorem sum_good_increments
    (q : ℕ) (hq : 1 ≤ q) (A G : Finset ℕ) (m : ℕ → ℕ) (u : ℕ → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hA : A ⊆ Finset.range q) (hG : G ⊆ A)
    (hm : ∀ k ∈ A, 1 ≤ m k)
    (hu : ∀ a b : ℕ, a ≤ b → b ≤ q → u a ≤ u b)
    (hbad : ((A \ G).card : ℝ) / (q : ℝ) ≤ δ)
    (hinc : ∀ k ∈ G, (1 + 1 / (m k : ℝ) - δ) / (q : ℝ) ≤ u (k + 1) - u k) :
    (∑ k ∈ A, (1 + 1 / (m k : ℝ)) / (q : ℝ)) ≤ u q - u 0 + 3 * δ := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := hqpos.ne'
  have hGr : G ⊆ Finset.range q := hG.trans hA
  have hcard : (G.card : ℝ) ≤ q := by
    exact_mod_cast (Finset.card_le_card hGr).trans_eq (Finset.card_range q)
  have htel : ∀ n : ℕ, (∑ k ∈ Finset.range n, (u (k + 1) - u k)) = u n - u 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have hsub : (∑ k ∈ G, (u (k + 1) - u k)) ≤ u q - u 0 := by
    rw [← htel q]
    apply Finset.sum_le_sum_of_subset_of_nonneg hGr
    intro k hk _
    have hkq : k < q := Finset.mem_range.mp hk
    exact sub_nonneg.mpr (hu k (k + 1) (by omega) (by omega))
  have hgood : (∑ k ∈ G, (1 + 1 / (m k : ℝ)) / (q : ℝ)) ≤ u q - u 0 + δ := by
    calc
      _ ≤ ∑ k ∈ G, (u (k + 1) - u k + δ / (q : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hh := hinc k hk
        rw [sub_div] at hh
        linarith
      _ = (∑ k ∈ G, (u (k + 1) - u k)) + (G.card : ℝ) * (δ / (q : ℝ)) := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ u q - u 0 + (q : ℝ) * (δ / (q : ℝ)) := by
        gcongr
      _ = u q - u 0 + δ := by field_simp
  have hweight : ∀ k ∈ A, (1 + 1 / (m k : ℝ)) / (q : ℝ) ≤ 2 / (q : ℝ) := by
    intro k hk
    have hmreal : (1 : ℝ) ≤ m k := by exact_mod_cast hm k hk
    have hmpos : (0 : ℝ) < m k := by linarith
    have hinv : 1 / (m k : ℝ) ≤ 1 := (div_le_one hmpos).mpr hmreal
    exact div_le_div_of_nonneg_right (by linarith) hqpos.le
  have hdiscard : (∑ k ∈ A \ G, (1 + 1 / (m k : ℝ)) / (q : ℝ)) ≤ 2 * δ := by
    calc
      _ ≤ ∑ _k ∈ A \ G, 2 / (q : ℝ) :=
        Finset.sum_le_sum fun k hk => hweight k (Finset.mem_sdiff.mp hk).1
      _ = 2 * (((A \ G).card : ℝ) / (q : ℝ)) := by simp; ring
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hbad (by norm_num)
  have hsplit : (∑ k ∈ A \ G, (1 + 1 / (m k : ℝ)) / (q : ℝ)) +
      (∑ k ∈ G, (1 + 1 / (m k : ℝ)) / (q : ℝ)) =
      ∑ k ∈ A, (1 + 1 / (m k : ℝ)) / (q : ℝ) :=
    Finset.sum_sdiff hG
  linarith

end Submission.Obl.k4_matching_refinement_exponent
