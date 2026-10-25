-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ExponentialRankFlow.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.RankFlow

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset

private theorem weighted_edge_potential_identity {α : Type*} [Fintype α]
    (R : α → α → Prop) [DecidableRel R] (w : α → ℝ) (k : ℝ) :
    (∑ i, ∑ j, if R i j then w j-k*w i else 0) =
      ∑ i, w i*((∑ j, if R j i then (1:ℝ) else 0)-
        k*(∑ j, if R i j then (1:ℝ) else 0)) := by
  have hsplit : (∑ i, ∑ j, if R i j then w j-k*w i else 0) =
      (∑ i, ∑ j, if R i j then w j else 0)-
      (∑ i, ∑ j, if R i j then k*w i else 0) := by
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  rw [hsplit]
  simp_rw [mul_sub, Finset.mul_sum, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_comm
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring

/-- An exponential rank potential permits a fixed multiplicative loss in
the local incoming/outgoing balance. -/
theorem edge_count_le_exp_rank_mul_budget {α : Type*} [Fintype α]
    (R : α → α → Prop) [DecidableRel R] (r : α → ℕ) (h : ℕ) {k : ℝ}
    (hk : 1 ≤ k) (hr : ∀ i, r i ≤ h) (hdesc : ∀ i j, R i j → r j<r i)
    (b : α → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hbudget : ∀ i, (∑ j, if R j i then (1:ℝ) else 0)-
      (k-1)*(∑ j, if R i j then (1:ℝ) else 0) ≤ b i) :
    (∑ i, ∑ j, if R i j then (1:ℝ) else 0) ≤ k^h*∑ i, b i := by
  let w : α → ℝ := fun i => k^(h-r i)
  have hk0 : 0 ≤ k := by linarith
  have hw : ∀ i, 0 ≤ w i := fun i => pow_nonneg hk0 _
  have hwone : ∀ i, 1 ≤ w i := fun i => one_le_pow₀ hk
  have hwupper : ∀ i, w i ≤ k^h := fun i => pow_le_pow_right₀ hk (Nat.sub_le _ _)
  have hwstep : ∀ i j, R i j → k*w i ≤ w j := by
    intro i j hij
    have hdegree : h-r i+1 ≤ h-r j := by have := hdesc i j hij; have := hr i; omega
    have hp := pow_le_pow_right₀ hk hdegree
    simpa only [w, pow_succ, mul_comm] using hp
  calc
    (∑ i, ∑ j, if R i j then (1:ℝ) else 0) ≤
        ∑ i, ∑ j, if R i j then w j-(k-1)*w i else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : R i j
      · simp only [hij, ite_true]
        nlinarith only [hwstep i j hij, hwone i]
      · simp only [hij, ite_false, le_refl]
    _ = ∑ i, w i*((∑ j, if R j i then (1:ℝ) else 0)-
        (k-1)*(∑ j, if R i j then (1:ℝ) else 0)) := weighted_edge_potential_identity R w (k-1)
    _ ≤ ∑ i, w i*b i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hbudget i) (hw i)
    _ ≤ ∑ i, k^h*b i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hwupper i) (hb i)
    _ = k^h*∑ i, b i := (Finset.mul_sum _ _ _).symm

/-- A bounded-rank descent controlling a fixed fraction of each symmetric
neighborhood bounds all its edges with an exponential-in-height constant. -/
theorem degree_sum_le_of_exp_rank_descent {α : Type*} [Fintype α]
    (S : α → α → Prop) [DecidableRel S] (hsymm : ∀ ⦃i j⦄, S i j → S j i)
    (r : α → ℕ) (h : ℕ) {k : ℝ} (hk : 1 ≤ k) (hr : ∀ i, r i ≤ h)
    (b : α → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hpart : ∀ i, (∑ j, if S i j then (1:ℝ) else 0) ≤
      k*(∑ j, if S i j ∧ r j<r i then (1:ℝ) else 0)+b i) :
    (∑ i, ∑ j, if S i j then (1:ℝ) else 0) ≤ (k^(h+1)+1)*∑ i, b i := by
  classical
  let R : α → α → Prop := fun i j => S i j ∧ r j<r i
  have hbudget : ∀ i, (∑ j, if R j i then (1:ℝ) else 0)-
      (k-1)*(∑ j, if R i j then (1:ℝ) else 0) ≤ b i := by
    intro i
    have hboth : (∑ j, if R j i then (1:ℝ) else 0)+
        (∑ j, if R i j then (1:ℝ) else 0) ≤
        ∑ j, if S i j then (1:ℝ) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : S i j
      · have hji := hsymm hij
        dsimp [R]
        simp only [hij, hji, true_and, ite_true]
        by_cases hlt : r i<r j
        · have hnot : ¬r j<r i := by omega
          simp [hlt, hnot]
        · simp only [hlt, ite_false, zero_add]
          split_ifs <;> norm_num
      · have hji : ¬S j i := fun hji => hij (hsymm hji)
        simp only [R, hij, hji, false_and, ite_false, zero_add, le_refl]
    have hh := hpart i
    change (∑ j, if S i j then (1:ℝ) else 0) ≤
      k*(∑ j, if R i j then (1:ℝ) else 0)+b i at hh
    nlinarith only [hboth, hh]
  have hflow := edge_count_le_exp_rank_mul_budget R r h hk hr (fun i j hij => hij.2)
    b hb hbudget
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset α)) => hpart i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  change (∑ i, ∑ j, if S i j then (1:ℝ) else 0) ≤
    k*(∑ i, ∑ j, if R i j then (1:ℝ) else 0)+(∑ i, b i) at hsum
  have hmult := mul_le_mul_of_nonneg_left hflow (show 0 ≤ k by linarith)
  rw [pow_succ]
  nlinarith only [hsum, hmult]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
