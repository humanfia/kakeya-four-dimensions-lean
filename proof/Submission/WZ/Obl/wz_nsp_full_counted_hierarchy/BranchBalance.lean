-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.BranchBalance.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators ENNReal

/-- The occupied children of the parent containing a leaf. -/
noncomputable def branchFiber {α β γ : Type*} [DecidableEq α] [DecidableEq γ]
    (S : Finset α) (p : α → β) (q : α → γ) (i : α) : Finset γ :=
  (leafFiber S p i).image q

/-- Partition a parent leaf fiber into its occupied child fibers. -/
theorem leaf_card_eq_sum_child_cards {α β γ : Type*} [DecidableEq α] [DecidableEq γ]
    (S : Finset α) (p : α → β) (q : α → γ)
    (hpq : ∀ a b, q a = q b → p a = p b) (i : α) :
    (leafFiber S p i).card =
      ∑ b ∈ branchFiber S p q i, (S.filter fun a => q a = b).card := by
  classical
  have hmaps : ∀ a ∈ leafFiber S p i, q a ∈ branchFiber S p q i := by
    intro a ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hs := Finset.card_eq_sum_card_fiberwise hmaps
  apply hs.trans
  apply Finset.sum_congr rfl
  intro b hb
  apply congrArg Finset.card
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨haS, hpa⟩ := Finset.mem_filter.mp ha
  ext c
  simp only [Finset.mem_filter, leafFiber]
  constructor
  · rintro ⟨⟨hc, _⟩, hq⟩
    exact ⟨hc, hq⟩
  · rintro ⟨hc, hq⟩
    exact ⟨⟨hc, (hpq c a hq).trans hpa⟩, hq⟩

/-- Balancing leaf counts at two consecutive levels balances immediate
branching, with the square of the leaf-count ratio. -/
theorem branch_balance_of_leaf_balance {α β γ : Type*} [DecidableEq α] [DecidableEq γ]
    (S : Finset α) (p : α → β) (q : α → γ) {R : ℝ} (hR : 0 ≤ R)
    (hpq : ∀ a b, q a = q b → p a = p b)
    (hp : Balanced S p R) (hq : Balanced S q R) :
    ∀ i ∈ S, ∀ j ∈ S,
      ((branchFiber S p q i).card : ℝ) ≤ R ^ 2 * (branchFiber S p q j).card := by
  classical
  intro i hi j hj
  obtain ⟨t, ht, htmin⟩ := Finset.exists_min_image S (fun a => (leafFiber S q a).card) ⟨i, hi⟩
  let d : ℝ := (leafFiber S q t).card
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast leafFiber_pos q ht
  have hb (i : α) (hi : i ∈ S) :
      ((branchFiber S p q i).card : ℝ) * d ≤ (leafFiber S p i).card ∧
      (leafFiber S p i).card ≤ R * ((branchFiber S p q i).card * d) := by
    have he := leaf_card_eq_sum_child_cards S p q hpq i
    have hlow : ∀ b ∈ branchFiber S p q i,
        d ≤ ((S.filter fun a => q a = b).card : ℝ) := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      have hh : (leafFiber S q t).card ≤ (leafFiber S q a).card :=
        htmin a (Finset.mem_filter.mp ha).1
      have hf : (S.filter fun b => q b = q a) = leafFiber S q a := by
        ext b
        simp [leafFiber]
      rw [hf]
      exact Nat.cast_le.mpr hh
    have hhigh : ∀ b ∈ branchFiber S p q i,
        ((S.filter fun a => q a = b).card : ℝ) ≤ R * d := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      have hf : (S.filter fun b => q b = q a) = leafFiber S q a := by
        ext b
        simp [leafFiber]
      rw [hf]
      exact hq a (Finset.mem_filter.mp ha).1 t ht
    have hel : ((leafFiber S p i).card : ℝ) =
        ∑ b ∈ branchFiber S p q i, ((S.filter fun a => q a = b).card : ℝ) := by
      exact_mod_cast he
    constructor
    · rw [hel]
      simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hlow
    · rw [hel]
      have hh := Finset.sum_le_sum hhigh
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_left_comm] using hh
  have hi' := hb i hi
  have hj' := hb j hj
  have hparent := hp i hi j hj
  apply le_of_mul_le_mul_right (a := d)
  · calc
      ((branchFiber S p q i).card : ℝ) * d ≤ (leafFiber S p i).card := hi'.1
      _ ≤ R * (leafFiber S p j).card := hparent
      _ ≤ R * (R * ((branchFiber S p q j).card * d)) := mul_le_mul_of_nonneg_left hj'.2 hR
      _ = (R ^ 2 * (branchFiber S p q j).card) * d := by ring
  · exact hd

/-- The accepted nested leaf regularizer also yields factor-two regular
immediate branches, at the same bounded number of pigeonhole losses. -/
theorem regularize_branches {α : Type*} [DecidableEq α]
    {β : ℕ → Type*} [∀ j, DecidableEq (β j)]
    (p : ∀ j, α → β j) (J q n : ℕ) (hq : 0 < q)
    (color : ℕ → Fin q)
    (hcolor : ∀ a b : ℕ, 0 < a → a ≤ n → 0 < b → b ≤ n →
      color a = color b → (a : ℝ) ≤ (4 / 3 : ℝ) * b)
    (hnest : ∀ j k, j ≤ k → k < J + 1 → ∀ i i', p k i = p k i' → p j i = p j i')
    (U : Finset α) (hU : U.card ≤ n) (hUne : U.Nonempty) :
    ∃ S : Finset α, S ⊆ U ∧ S.Nonempty ∧ U.card ≤ q ^ (J + 1) * S.card ∧
      ∀ j, j < J → ∃ M : ℝ, 1 ≤ M ∧ ∀ i ∈ S,
        M / 2 ≤ ((branchFiber S (p j) (p (j + 1)) i).card : ℝ) ∧
        ((branchFiber S (p j) (p (j + 1)) i).card : ℝ) ≤ M := by
  classical
  obtain ⟨S, hSU, hmass, hbal⟩ := regularize_nested p (J + 1) q n hq (4 / 3)
    color hcolor hnest U hU (fun _ => 1)
  have hmass' : U.card ≤ q ^ (J + 1) * S.card := by
    have hh : (U.card : ℝ≥0∞) ≤ (q : ℝ≥0∞) ^ (J + 1) * S.card := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hmass
    exact_mod_cast hh
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    have hu := Finset.card_pos.mpr hUne
    by_contra hn
    have he : S.card = 0 := by omega
    rw [he, mul_zero] at hmass'
    omega
  refine ⟨S, hSU, hSne, hmass', ?_⟩
  intro j hj
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image S
    (fun i => (branchFiber S (p j) (p (j + 1)) i).card) hSne
  have htpos : 0 < (branchFiber S (p j) (p (j + 1)) t).card := by
    apply Finset.card_pos.mpr
    refine ⟨p (j + 1) t, Finset.mem_image.mpr ⟨t, ?_, rfl⟩⟩
    simp only [leafFiber, Finset.mem_filter, ht, and_self]
  refine ⟨(branchFiber S (p j) (p (j + 1)) t).card, ?_, ?_⟩
  · exact_mod_cast htpos
  · intro i hi
    refine ⟨?_, Nat.cast_le.mpr (hmax i hi)⟩
    have hb := branch_balance_of_leaf_balance S (p j) (p (j + 1))
      (show (0 : ℝ) ≤ 4 / 3 by norm_num)
      (hnest j (j + 1) (by omega) (by omega))
      (hbal j (by omega)) (hbal (j + 1) (by omega)) t ht i hi
    have hn : (0 : ℝ) ≤ (branchFiber S (p j) (p (j + 1)) i).card := Nat.cast_nonneg _
    norm_num at hb
    linarith

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
