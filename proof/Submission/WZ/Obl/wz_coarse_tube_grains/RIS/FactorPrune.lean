-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FactorPrune.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Iterated pruning of a bipartite graph (WZ Lemma 4.7)

Removing, one at a time, vertices whose current degree is below a fixed threshold (`tA` on the
left, `tB` on the right) ends in an induced subgraph in which every vertex has degree at least
its threshold, and which has lost fewer than `tA #A + tB #B` edges.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open Finset

variable {α β : Type*} (E : α → β → Prop) [DecidableRel E]

/-- The number of edges between `A` and `B`. -/
def edges (A : Finset α) (B : Finset β) : ℝ := ∑ a ∈ A, ((B.filter (E a)).card : ℝ)

/-- The degree of `a` towards `B`. -/
def degL (a : α) (B : Finset β) : ℝ := ((B.filter (E a)).card : ℝ)

/-- The degree of `b` towards `A`. -/
def degR (b : β) (A : Finset α) : ℝ := ((A.filter fun a => E a b).card : ℝ)

variable {E}

theorem edges_eq_sum_degR (A : Finset α) (B : Finset β) :
    edges E A B = ∑ b ∈ B, degR E b A := by
  unfold edges degR
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Finset.sum_comm

theorem edges_erase_left [DecidableEq α] (A : Finset α) (B : Finset β) {a : α} (ha : a ∈ A) :
    edges E A B = edges E (A.erase a) B + degL E a B := by
  unfold edges degL
  rw [← Finset.sum_erase_add _ _ ha]

theorem edges_erase_right [DecidableEq β] (A : Finset α) (B : Finset β) {b : β} (hb : b ∈ B) :
    edges E A B = edges E A (B.erase b) + degR E b A := by
  rw [edges_eq_sum_degR, edges_eq_sum_degR, ← Finset.sum_erase_add _ _ hb]

theorem degL_nonneg (a : α) (B : Finset β) : 0 ≤ degL E a B := Nat.cast_nonneg _

theorem degL_mono {a : α} {B B' : Finset β} (h : B ⊆ B') : degL E a B ≤ degL E a B' := by
  unfold degL
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem degR_mono {b : β} {A A' : Finset α} (h : A ⊆ A') : degR E b A ≤ degR E b A' := by
  unfold degR
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- **Iterated graph pruning.** -/
theorem prune [DecidableEq α] [DecidableEq β] {tA tB : ℝ} (htA : 0 ≤ tA) (htB : 0 ≤ tB) :
    ∀ (A : Finset α) (B : Finset β), ∃ A' ⊆ A, ∃ B' ⊆ B,
      (∀ a ∈ A', tA ≤ degL E a B') ∧ (∀ b ∈ B', tB ≤ degR E b A') ∧
      edges E A B ≤ edges E A' B' + tA * A.card + tB * B.card := by
  intro A B
  induction hn : A.card + B.card using Nat.strong_induction_on generalizing A B with
  | _ n ih =>
  by_cases hA : ∃ a ∈ A, degL E a B < tA
  · obtain ⟨a, ha, hlt⟩ := hA
    have hlt' : (A.erase a).card + B.card < n := by
      rw [← hn, Finset.card_erase_of_mem ha]
      have := Finset.card_pos.mpr ⟨a, ha⟩
      omega
    obtain ⟨A', hA', B', hB', h1, h2, h3⟩ := ih _ hlt' (A.erase a) B rfl
    refine ⟨A', hA'.trans (Finset.erase_subset _ _), B', hB', h1, h2, ?_⟩
    rw [edges_erase_left A B ha]
    have hcard : ((A.erase a).card : ℝ) + 1 = A.card := by
      rw [Finset.card_erase_of_mem ha]
      have := Finset.card_pos.mpr ⟨a, ha⟩
      rw [Nat.cast_sub (by omega)]
      push_cast; ring
    nlinarith
  by_cases hB : ∃ b ∈ B, degR E b A < tB
  · obtain ⟨b, hb, hlt⟩ := hB
    have hlt' : A.card + (B.erase b).card < n := by
      rw [← hn, Finset.card_erase_of_mem hb]
      have := Finset.card_pos.mpr ⟨b, hb⟩
      omega
    obtain ⟨A', hA', B', hB', h1, h2, h3⟩ := ih _ hlt' A (B.erase b) rfl
    refine ⟨A', hA', B', hB'.trans (Finset.erase_subset _ _), h1, h2, ?_⟩
    rw [edges_erase_right A B hb]
    have hcard : ((B.erase b).card : ℝ) + 1 = B.card := by
      rw [Finset.card_erase_of_mem hb]
      have := Finset.card_pos.mpr ⟨b, hb⟩
      rw [Nat.cast_sub (by omega)]
      push_cast; ring
    nlinarith
  push Not at hA hB
  refine ⟨A, subset_rfl, B, subset_rfl, hA, hB, ?_⟩
  have : 0 ≤ tA * A.card + tB * B.card := by positivity
  linarith

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
