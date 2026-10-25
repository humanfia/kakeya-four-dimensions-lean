-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.BalancedPruning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.BranchBalance

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open WangZahlLot.Obl.wz_tower_balanced_refinement
open WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

/-- Global retention between balanced leaf partitions gives retention in every
occupied parent. This controls denominators in relative slab bounds. -/
theorem balanced_leaf_retention {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U S : Finset α) (p : α → β) (hSU : S ⊆ U)
    {R T lam : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (hlam : 0 ≤ lam)
    (hU : Balanced U p R) (hS : Balanced S p T)
    (hmass : lam * U.card ≤ S.card) {i : α} (hi : i ∈ S) :
    lam * (leafFiber U p i).card ≤ R * T * (leafFiber S p i).card := by
  classical
  let V := U.image p
  have hV : 0 < (V.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨p i, Finset.mem_image.mpr ⟨i, hSU hi, rfl⟩⟩
  have hcardU : (U.card : ℝ) = ∑ b ∈ V, ((U.filter fun a => p a = b).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩ : ∀ a ∈ U, p a ∈ V)
  have hcardS : (S.card : ℝ) = ∑ b ∈ V, ((S.filter fun a => p a = b).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (fun a ha => Finset.mem_image.mpr ⟨a, hSU ha, rfl⟩ : ∀ a ∈ S, p a ∈ V)
  have hu : (V.card : ℝ) * (leafFiber U p i).card ≤ R * U.card := by
    rw [hcardU, Finset.mul_sum]
    have hh : ∀ b ∈ V, ((leafFiber U p i).card : ℝ) ≤
        R * (U.filter fun a => p a = b).card := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      have hf : (U.filter fun b => p b = p a) = leafFiber U p a := by
        ext b
        simp [leafFiber]
      rw [hf]
      exact hU i (hSU hi) a ha
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hh
  have hs : (S.card : ℝ) ≤ V.card * (T * (leafFiber S p i).card) := by
    rw [hcardS]
    have hh : ∀ b ∈ V, ((S.filter fun a => p a = b).card : ℝ) ≤
        T * (leafFiber S p i).card := by
      intro b hb
      by_cases hn : (S.filter fun a => p a = b).Nonempty
      · obtain ⟨a, ha⟩ := hn
        obtain ⟨haS, rfl⟩ := Finset.mem_filter.mp ha
        have hf : (S.filter fun b => p b = p a) = leafFiber S p a := by
          ext b
          simp [leafFiber]
        rw [hf]
        exact hS a haS i hi
      · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero]
        positivity
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hh
  apply le_of_mul_le_mul_left (a := (V.card : ℝ)) _ hV
  calc
    (V.card : ℝ) * (lam * (leafFiber U p i).card) =
        lam * ((V.card : ℝ) * (leafFiber U p i).card) := by ring
    _ ≤ lam * (R * U.card) := mul_le_mul_of_nonneg_left hu hlam
    _ = R * (lam * U.card) := by ring
    _ ≤ R * S.card := mul_le_mul_of_nonneg_left hmass hR
    _ ≤ R * (V.card * (T * (leafFiber S p i).card)) := mul_le_mul_of_nonneg_left hs hR
    _ = (V.card : ℝ) * (R * T * (leafFiber S p i).card) := by ring

/-- A retained fraction of leaves in a parent retains a comparable fraction of
its occupied children, provided the old child leaf counts were balanced. -/
theorem branch_retention_of_leaf_retention {α β γ : Type*}
    [DecidableEq α] [DecidableEq γ]
    (U S : Finset α) (p : α → β) (q : α → γ) (hSU : S ⊆ U)
    (hpq : ∀ a b, q a = q b → p a = p b)
    {R A lam : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) (hlam : 0 ≤ lam)
    (hbal : Balanced U q R) {i : α} (hi : i ∈ S)
    (hret : lam * (leafFiber U p i).card ≤ A * (leafFiber S p i).card) :
    lam * (branchFiber U p q i).card ≤ A * R * (branchFiber S p q i).card := by
  classical
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image U
    (fun a => (leafFiber U q a).card) ⟨i, hSU hi⟩
  let d : ℝ := (leafFiber U q t).card
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast leafFiber_pos q ht
  have hu : ((branchFiber U p q i).card : ℝ) * d ≤ (leafFiber U p i).card := by
    have he : ((leafFiber U p i).card : ℝ) =
        ∑ b ∈ branchFiber U p q i, ((U.filter fun a => q a = b).card : ℝ) := by
      exact_mod_cast leaf_card_eq_sum_child_cards U p q hpq i
    rw [he]
    have hh : ∀ b ∈ branchFiber U p q i, d ≤ ((U.filter fun a => q a = b).card : ℝ) := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      have hf : (U.filter fun b => q b = q a) = leafFiber U q a := by
        ext b
        simp [leafFiber]
      rw [hf]
      exact Nat.cast_le.mpr (hmin a (Finset.mem_filter.mp ha).1)
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hh
  have hs : ((leafFiber S p i).card : ℝ) ≤ (branchFiber S p q i).card * (R * d) := by
    have he : ((leafFiber S p i).card : ℝ) =
        ∑ b ∈ branchFiber S p q i, ((S.filter fun a => q a = b).card : ℝ) := by
      exact_mod_cast leaf_card_eq_sum_child_cards S p q hpq i
    rw [he]
    have hh : ∀ b ∈ branchFiber S p q i, ((S.filter fun a => q a = b).card : ℝ) ≤ R * d := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      calc
        _ ≤ ((U.filter fun b => q b = q a).card : ℝ) := by
          exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hSU))
        _ ≤ R * d := by
          have hf : (U.filter fun b => q b = q a) = leafFiber U q a := by
            ext b
            simp [leafFiber]
          rw [hf]
          exact hbal a (hSU (Finset.mem_filter.mp ha).1) t ht
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hh
  apply le_of_mul_le_mul_right (a := d) _ hd
  calc
    (lam * (branchFiber U p q i).card) * d = lam * ((branchFiber U p q i).card * d) := by ring
    _ ≤ lam * (leafFiber U p i).card := mul_le_mul_of_nonneg_left hu hlam
    _ ≤ A * (leafFiber S p i).card := hret
    _ ≤ A * ((branchFiber S p q i).card * (R * d)) := mul_le_mul_of_nonneg_left hs hA
    _ = (A * R * (branchFiber S p q i).card) * d := by ring

theorem balanced_branch_retention {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (U S : Finset α) (p : α → β) (q : α → γ) (hSU : S ⊆ U)
    (hpq : ∀ a b, q a = q b → p a = p b)
    {R T C lam : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hU : Balanced U p R) (hS : Balanced S p T) (hq : Balanced U q C)
    (hmass : lam * U.card ≤ S.card) {i : α} (hi : i ∈ S) :
    lam * (branchFiber U p q i).card ≤ R * T * C * (branchFiber S p q i).card :=
  branch_retention_of_leaf_retention U S p q hSU hpq hC (mul_nonneg hR hT) hlam hq hi
    (balanced_leaf_retention U S p hSU hR hT hlam hU hS hmass hi)

end WangZahlLot.Obl.wz_multiscale_finite_tower
