import Submission.Obl.k4_oss_weighted_level_transfer.Mixture

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

/-- Coarse power levels cover every weight, with a uniform small tail. -/
lemma power_cover (b p : ℝ) (hb : 0 ≤ b) (hp : p ≤ 1) (M : ℕ) :
    p ≤ (∑ k ∈ Finset.range M, if b ^ (k + 1) ≤ p then b ^ k else 0) + b ^ M := by
  induction M with
  | zero => simpa using hp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    by_cases h : b ^ (M + 1) ≤ p
    · rw [if_pos h]
      linarith [pow_nonneg hb (M + 1)]
    · rw [if_neg h]
      have hs : 0 ≤ ∑ k ∈ Finset.range M,
          if b ^ (k + 1) ≤ p then b ^ k else 0 := by
        apply Finset.sum_nonneg
        intro k hk
        split <;> positivity
      linarith [lt_of_not_ge h]

noncomputable def level (S : Finset ℝ) (p : ℝ → ℝ) (b : ℝ) (k : ℕ) : Finset ℝ := by
  classical
  exact S.filter (fun x => b ^ (k + 1) ≤ p x)

lemma level_subset (S : Finset ℝ) (p : ℝ → ℝ) (b : ℝ) (k : ℕ) :
    level S p b k ⊆ S := by
  classical
  exact Finset.filter_subset _ _

lemma weight_le_one {S : Finset ℝ} {p : ℝ → ℝ}
    (hp : ∀ x ∈ S, 0 ≤ p x) (hmass : ∑ x ∈ S, p x ≤ 1) {x : ℝ} (hx : x ∈ S) :
    p x ≤ 1 := (Finset.single_le_sum hp hx).trans hmass

lemma level_mass_bound {S : Finset ℝ} {p : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hp : ∀ x ∈ S, 0 ≤ p x) (hmass : ∑ x ∈ S, p x ≤ 1) (k : ℕ) :
    b ^ k * ((level S p b k).card : ℝ) ≤ 1 / b := by
  classical
  have hlow : b ^ (k + 1) * ((level S p b k).card : ℝ) ≤
      ∑ x ∈ level S p b k, p x := by
    calc
      _ = ∑ _x ∈ level S p b k, b ^ (k + 1) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun x hx => (Finset.mem_filter.mp hx).2)
  have hsum : ∑ x ∈ level S p b k, p x ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (level_subset _ _ _ _)
      (fun x hx _ => hp x hx)).trans hmass
  apply (le_div_iff₀ hb).mpr
  rw [pow_succ] at hlow
  nlinarith

lemma level_square_bound {S : Finset ℝ} {p : ℝ → ℝ} {b Q : ℝ}
    (hb : 0 < b) (hQ : ∑ x ∈ S, (p x) ^ 2 ≤ Q) (k : ℕ) :
    (b ^ k) ^ 2 * ((level S p b k).card : ℝ) ≤ Q / b ^ 2 := by
  classical
  have hlow : (b ^ (k + 1)) ^ 2 * ((level S p b k).card : ℝ) ≤
      ∑ x ∈ level S p b k, (p x) ^ 2 := by
    calc
      _ = ∑ _x ∈ level S p b k, (b ^ (k + 1)) ^ 2 := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        have hh := (Finset.mem_filter.mp hx).2
        exact pow_le_pow_left₀ (pow_nonneg hb.le _) hh 2
  have hsum : ∑ x ∈ level S p b k, (p x) ^ 2 ≤ Q :=
    (Finset.sum_le_sum_of_subset_of_nonneg (level_subset _ _ _ _)
      (fun x hx _ => sq_nonneg _)).trans hQ
  apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
  rw [show b ^ (k + 1) = b ^ k * b from pow_succ b k, mul_pow] at hlow
  nlinarith

lemma level_local_bound {S : Finset ℝ} {p : ℝ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hp : ∀ x ∈ S, 0 ≤ p x) (k : ℕ) (x u : ℝ) :
    b ^ (k + 1) * (((level S p b k).filter (fun y => dist y x ≤ u)).card : ℝ) ≤
      ∑ y ∈ S.filter (fun y => dist y x ≤ u), p y := by
  classical
  let L := (level S p b k).filter (fun y => dist y x ≤ u)
  have hsub : L ⊆ S.filter (fun y => dist y x ≤ u) := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨hy, hyx⟩
    exact Finset.mem_filter.mpr ⟨level_subset _ _ _ _ hy, hyx⟩
  calc
    _ = ∑ _y ∈ L, b ^ (k + 1) := by simp [L, mul_comm]
    _ ≤ ∑ y ∈ L, p y := by
      apply Finset.sum_le_sum
      intro y hy
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun y hy _ => hp y (Finset.mem_filter.mp hy).1)

end Submission.Obl.k4_oss_weighted_level_transfer
