/- Adapted from: here:o247 (session x0870, original proofs in commits
4fa3d421, 60e815aa, 71be63c4, and 30be2d73). -/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

namespace Submission.Lib.K4OriginalStatePreparation

open Finset

noncomputable section

open scoped Classical

/-- Choosing a representative from positive original weight costs at most
the weighted average disagreement. The estimate is unnormalized. -/
theorem weighted_representative {ι : Type*} [Fintype ι]
    (w cost : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hm : 0 < ∑ i, w i) :
    ∃ i, 0 < w i ∧ (∑ j, w j) * cost i ≤ ∑ j, w j * cost j := by
  classical
  let S : Finset ι := univ.filter (fun i => 0 < w i)
  have hS : S.Nonempty := by
    obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff_of_nonneg (fun i _ => hw i) |>.mp hm
    exact ⟨i, by simp only [S, mem_filter, mem_univ, true_and]; exact hi⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S cost hS
  refine ⟨i, (mem_filter.mp hi).2, ?_⟩
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : 0 < w j
  · exact mul_le_mul_of_nonneg_left (hmin j (by simp [S, hj])) (hw j)
  · have hj0 : w j = 0 := le_antisymm (le_of_not_gt hj) (hw j)
    simp [hj0]

/-- At each finite state choose a positive-weight representative, when the
state has positive mass. The loss is bounded by disagreement between two
independent samples conditional on that original state. -/
theorem state_representatives {Q ι : Type*} [Fintype Q] [Fintype ι] [Nonempty ι]
    (w : Q → ι → ℝ) (R : Q → ι → ι → Prop) (hw : ∀ q i, 0 ≤ w q i) :
    ∃ center : Q → ι,
      (∀ q, 0 < ∑ i, w q i → 0 < w q (center q)) ∧
      (∀ q, (∑ i, if R q i (center q) then 0 else w q i) ≤
        (∑ j, w q j * ∑ i, if R q i j then 0 else w q i) / (∑ i, w q i)) := by
  classical
  let cost : Q → ι → ℝ := fun q j => ∑ i, if R q i j then 0 else w q i
  have hex (q : Q) : ∃ j, (0 < ∑ i, w q i → 0 < w q j) ∧
      cost q j ≤ (∑ j, w q j * cost q j) / (∑ i, w q i) := by
    by_cases hm : 0 < ∑ i, w q i
    · obtain ⟨j, hj, hcost⟩ := weighted_representative (w q) (cost q) (hw q) hm
      exact ⟨j, fun _ => hj, (le_div_iff₀ hm).mpr (by nlinarith)⟩
    · have hm0 : ∑ i, w q i = 0 :=
        le_antisymm (le_of_not_gt hm) (Finset.sum_nonneg fun i _ => hw q i)
      have hw0 (i : ι) : w q i = 0 := by
        apply le_antisymm _ (hw q i)
        calc
          w q i ≤ ∑ i, w q i := Finset.single_le_sum (fun j _ => hw q j) (mem_univ i)
          _ = 0 := hm0
      refine ⟨Classical.choice inferInstance, fun h => (hm h).elim, ?_⟩
      simp [cost, hw0]
  choose center hcenter using hex
  exact ⟨center, fun q => (hcenter q).1, fun q => (hcenter q).2⟩

/-- Discard states that lose more than half their mass, as well as events
that disagree with their representative. The total loss is at most twice
the sum of the conditional pair-disagreement masses. Every occupied state
keeps at least half of its original mass. -/
theorem state_consensus {Q ι : Type*} [Fintype Q] [Fintype ι] [Nonempty ι]
    (w : Q → ι → ℝ) (R : Q → ι → ι → Prop) (hw : ∀ q i, 0 ≤ w q i) :
    ∃ (center : Q → ι) (keep : Q → ι → Prop),
      (∀ q i, keep q i → R q i (center q)) ∧
      (∀ q, (∑ i, if keep q i then w q i else 0) = 0 ∨
        (∑ i, w q i) / 2 ≤ ∑ i, if keep q i then w q i else 0) ∧
      (∀ q i, keep q i → 0 < ∑ j, w q j → 0 < w q (center q)) ∧
      (∑ q, ∑ i, w q i) ≤ (∑ q, ∑ i, if keep q i then w q i else 0) +
        2 * ∑ q, (∑ j, w q j * ∑ i, if R q i j then 0 else w q i) /
          (∑ i, w q i) := by
  classical
  obtain ⟨center, hcenter, hcost⟩ := state_representatives w R hw
  let mass : Q → ℝ := fun q => ∑ i, w q i
  let loss : Q → ℝ := fun q => ∑ i, if R q i (center q) then 0 else w q i
  let keep : Q → ι → Prop := fun q i => loss q ≤ mass q / 2 ∧ R q i (center q)
  have hsplit (q : Q) : mass q =
      (∑ i, if R q i (center q) then w q i else 0) + loss q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : R q i (center q) <;> simp [h]
  have hmass (q : Q) : mass q ≤ (∑ i, if keep q i then w q i else 0) +
      2 * ((∑ j, w q j * ∑ i, if R q i j then 0 else w q i) / mass q) := by
    have hloss : loss q ≤ (∑ j, w q j * ∑ i, if R q i j then 0 else w q i) /
        mass q := hcost q
    have hloss0 : 0 ≤ loss q := Finset.sum_nonneg fun i _ => by
      split_ifs <;> first | exact le_rfl | exact hw q i
    by_cases h : loss q ≤ mass q / 2
    · simp only [keep, h, true_and]
      linarith [hsplit q]
    · simp only [keep, h, false_and, ↓reduceIte, Finset.sum_const_zero]
      linarith
  refine ⟨center, keep, fun q i hi => hi.2, ?_, ?_, ?_⟩
  · intro q
    by_cases h : loss q ≤ mass q / 2
    · right
      simp only [keep, h, true_and]
      linarith [hsplit q]
    · left
      simp [keep, h]
  · intro q i _ hm
    exact hcenter q hm
  · calc
      _ ≤ ∑ q, ((∑ i, if keep q i then w q i else 0) +
          2 * ((∑ j, w q j * ∑ i, if R q i j then 0 else w q i) / mass q)) :=
        Finset.sum_le_sum fun q _ => hmass q
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro q _
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : keep q i <;> simp [hi]
        · rfl

/-- Keeping half of each occupied state transfers its original palette
bound with a factor two. Each velocity contribution is only decreased. -/
theorem consensus_palette_bound {ι V : Type*} [Fintype ι]
    (w : ι → ℝ) (wv : V → ι → ℝ) (keep : ι → Prop) (K : ℝ) (π : V → ℝ)
    (hK : 0 ≤ K) (hπ : ∀ v, 0 ≤ π v) (hwv : ∀ v i, 0 ≤ wv v i)
    (hsub : ∀ v i, wv v i ≤ w i)
    (hhalf : (∑ i, if keep i then w i else 0) = 0 ∨
      (∑ i, w i) / 2 ≤ ∑ i, if keep i then w i else 0)
    (hcap : ∀ v, (∑ i, wv v i) ≤ K * (∑ i, w i) * π v) :
    ∀ v, (∑ i, if keep i then wv v i else 0) ≤
      (2 * K) * (∑ i, if keep i then w i else 0) * π v := by
  intro v
  have hle : (∑ i, if keep i then wv v i else 0) ≤
      ∑ i, if keep i then w i else 0 := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | exact hsub v i | rfl
  rcases hhalf with hzero | hhalf
  · rw [hzero, mul_zero, zero_mul]
    exact hle.trans_eq hzero
  · have hle' : (∑ i, if keep i then wv v i else 0) ≤ ∑ i, wv v i := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> first | rfl | exact hwv v i
    calc
      _ ≤ K * (∑ i, w i) * π v := hle'.trans (hcap v)
      _ ≤ K * (2 * ∑ i, if keep i then w i else 0) * π v :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith : (∑ i, w i) ≤
            2 * ∑ i, if keep i then w i else 0) hK) (hπ v)
      _ = _ := by ring

end

end Submission.Lib.K4OriginalStatePreparation
