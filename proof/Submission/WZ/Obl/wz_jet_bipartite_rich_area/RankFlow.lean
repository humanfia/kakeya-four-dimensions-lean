-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.RankFlow.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset

private theorem edge_potential_identity {α : Type*} [Fintype α]
    (R : α → α → Prop) [DecidableRel R] (w : α → ℝ) :
    (∑ i, ∑ j, if R i j then w j-w i else 0) =
      ∑ i, w i*((∑ j, if R j i then (1:ℝ) else 0)-
        (∑ j, if R i j then (1:ℝ) else 0)) := by
  have hsplit : (∑ i, ∑ j, if R i j then w j-w i else 0) =
      (∑ i, ∑ j, if R i j then w j else 0)-
      (∑ i, ∑ j, if R i j then w i else 0) := by
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  rw [hsplit]
  simp_rw [mul_sub, Finset.mul_sum, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

/-- A directed graph with a decreasing natural-number rank and a budget for
incoming minus outgoing degree has at most rank-height times total budget
edges. The proof sums the rank potential, so no injective charge is needed. -/
theorem edge_count_le_rank_mul_budget {α : Type*} [Fintype α]
    (R : α → α → Prop) [DecidableRel R] (r : α → ℕ) (h : ℕ)
    (hr : ∀ i, r i ≤ h) (hdesc : ∀ i j, R i j → r j < r i)
    (b : α → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hbudget : ∀ i,
      (∑ j, if R j i then (1:ℝ) else 0)-
      (∑ j, if R i j then (1:ℝ) else 0) ≤ b i) :
    (∑ i, ∑ j, if R i j then (1:ℝ) else 0) ≤ (h:ℝ)*∑ i, b i := by
  let w : α → ℝ := fun i => (h:ℝ)-(r i:ℝ)
  have hw : ∀ i, 0 ≤ w i := fun i => sub_nonneg.mpr (Nat.cast_le.mpr (hr i))
  have hwupper : ∀ i, w i ≤ h := by
    intro i
    dsimp [w]
    exact sub_le_self _ (Nat.cast_nonneg _)
  calc
    (∑ i, ∑ j, if R i j then (1:ℝ) else 0) ≤
        ∑ i, ∑ j, if R i j then w j-w i else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : R i j
      · simp only [hij, ite_true]
        have hh : (r j:ℝ)+1 ≤ (r i:ℝ) := by exact_mod_cast hdesc i j hij
        dsimp [w]
        linarith
      · simp only [hij, ite_false, le_refl]
    _ = ∑ i, w i*((∑ j, if R j i then (1:ℝ) else 0)-
        (∑ j, if R i j then (1:ℝ) else 0)) := edge_potential_identity R w
    _ ≤ ∑ i, w i*b i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hbudget i) (hw i)
    _ ≤ ∑ i, (h:ℝ)*b i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hwupper i) (hb i)
    _ = (h:ℝ)*∑ i, b i := (Finset.mul_sum _ _ _).symm

/-- If at least half of each vertex's neighbors have lower rank, up to a
local budget, the entire symmetric relation has a budget proportional to
the rank height. Equal-rank neighbors are allowed. -/
theorem degree_sum_le_of_rank_descent {α : Type*} [Fintype α]
    (S : α → α → Prop) [DecidableRel S] (hsymm : ∀ ⦃i j⦄, S i j → S j i)
    (r : α → ℕ) (h : ℕ) (hr : ∀ i, r i ≤ h)
    (b : α → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hhalf : ∀ i, (∑ j, if S i j then (1:ℝ) else 0) ≤
      2*(∑ j, if S i j ∧ r j<r i then (1:ℝ) else 0)+b i) :
    (∑ i, ∑ j, if S i j then (1:ℝ) else 0) ≤ ((2*h:ℕ)+1:ℝ)*∑ i, b i := by
  classical
  let R : α → α → Prop := fun i j => S i j ∧ r j<r i
  have hbudget : ∀ i, (∑ j, if R j i then (1:ℝ) else 0)-
      (∑ j, if R i j then (1:ℝ) else 0) ≤ b i := by
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
    have hh := hhalf i
    change (∑ j, if S i j then (1:ℝ) else 0) ≤
      2*(∑ j, if R i j then (1:ℝ) else 0)+b i at hh
    linarith
  have hflow := edge_count_le_rank_mul_budget R r h hr (fun i j hij => hij.2)
    b hb hbudget
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset α)) => hhalf i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  change (∑ i, ∑ j, if S i j then (1:ℝ) else 0) ≤
    2*(∑ i, ∑ j, if R i j then (1:ℝ) else 0)+(∑ i, b i) at hsum
  push_cast
  nlinarith only [hsum, hflow]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
