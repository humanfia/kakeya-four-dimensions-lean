import Mathlib

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open Classical

/-- Keep a label precisely when it and every ancestor down to its root pass. -/
def Kept {ι : Type*} (lev : ι → ℕ) (par : ι → ι) (good : ι → Prop) (b : ι) : Prop :=
  ∀ n, n ≤ lev b → good (par^[n] b)

theorem kept_good {ι : Type*} {lev : ι → ℕ} {par : ι → ι} {good : ι → Prop}
    {b : ι} (hb : Kept lev par good b) : good b := by
  simpa using hb 0 (Nat.zero_le _)

theorem kept_parent {ι : Type*} {lev : ι → ℕ} {par : ι → ι} {good : ι → Prop}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    {b : ι} (hb : Kept lev par good b) (hlev : 0 < lev b) : Kept lev par good (par b) := by
  intro n hn
  have hle : n + 1 ≤ lev b := by have := hpar b hlev; omega
  simpa only [Function.iterate_succ_apply] using hb (n + 1) hle

theorem kept_iff {ι : Type*} {lev : ι → ℕ} {par : ι → ι} {good : ι → Prop}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b) (b : ι) :
    Kept lev par good b ↔ good b ∧ (0 < lev b → Kept lev par good (par b)) := by
  constructor
  · intro hb
    exact ⟨kept_good hb, kept_parent hpar hb⟩
  · rintro ⟨hg, hp⟩ n hn
    cases n with
    | zero => simpa using hg
    | succ n =>
      have hb : 0 < lev b := by omega
      have hnp : n ≤ lev (par b) := by have := hpar b hb; omega
      simpa only [Function.iterate_succ_apply] using hp hb n hnp

/-- Charge a chosen collection of children to its chosen parents. -/
theorem parent_mass_charge {C : ℕ} (lev : Fin C → ℕ) (par : Fin C → Fin C)
    (mass : Fin C → ENNReal)
    (hbudget : ∀ a, (∑ b, if 0 < lev b ∧ par b = a then mass b else 0) ≤ mass a)
    (P : Fin C → Prop) [DecidablePred P] :
    (∑ b, if 0 < lev b ∧ P (par b) then mass b else 0) ≤
      ∑ a, if P a then mass a else 0 := by
  classical
  let f : Fin C → ENNReal := fun b => if 0 < lev b ∧ P (par b) then mass b else 0
  change (∑ b, f b) ≤ _
  rw [← Finset.sum_fiberwise Finset.univ par f]
  apply Finset.sum_le_sum
  intro a _
  have heq : (∑ b ∈ Finset.univ.filter (fun b => par b = a), f b) =
      if P a then (∑ b, if 0 < lev b ∧ par b = a then mass b else 0) else 0 := by
    rw [Finset.sum_filter]
    by_cases hPa : P a
    · simp only [hPa, ite_true]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hp : par b = a <;> simp [f, hp, hPa]
    · simp only [hPa, ite_false]
      apply Finset.sum_eq_zero
      intro b _
      by_cases hp : par b = a <;> simp [f, hp, hPa]
  rw [heq]
  split_ifs
  · exact hbudget a
  · exact le_rfl

/-- At any layer, removing every failed label and all its descendants costs
at most the total mass of all failed labels. -/
theorem forest_removed_mass_le {C : ℕ} (lev : Fin C → ℕ) (par : Fin C → Fin C)
    (mass : Fin C → ENNReal) (good : Fin C → Prop) [DecidablePred good]
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (hbudget : ∀ a, (∑ b, if 0 < lev b ∧ par b = a then mass b else 0) ≤ mass a)
    (i : ℕ) :
    (∑ b, if lev b = i ∧ ¬Kept lev par good b then mass b else 0) ≤
      ∑ b, if ¬good b then mass b else 0 := by
  classical
  have hstrong : ∀ i : ℕ,
      (∑ b, if lev b = i ∧ ¬Kept lev par good b then mass b else 0) ≤
        ∑ b, if lev b ≤ i ∧ ¬good b then mass b else 0 := by
    intro i
    induction i with
    | zero =>
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : lev b = 0
      · have hk : Kept lev par good b ↔ good b := by
          rw [kept_iff hpar]
          simp [hb]
        simp [hb, hk]
      · simp [hb, Nat.pos_of_ne_zero hb]
    | succ i ih =>
      have hsplit :
          (∑ b, if lev b = i + 1 ∧ ¬Kept lev par good b then mass b else 0) ≤
          (∑ b, if lev b = i + 1 ∧ ¬good b then mass b else 0) +
          ∑ b, if 0 < lev b ∧ (lev (par b) = i ∧ ¬Kept lev par good (par b)) then mass b else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro b _
        by_cases hb : lev b = i + 1
        · have hpos : 0 < lev b := by omega
          have hlevp : lev (par b) = i := by have := hpar b hpos; omega
          by_cases hg : good b
          · have hk : Kept lev par good b ↔ Kept lev par good (par b) := by
              rw [kept_iff hpar]
              simp [hg, hpos]
            simp [hb, hpos, hlevp, hg, hk]
          · have hnk : ¬Kept lev par good b := fun hk => hg (kept_good hk)
            simp only [hb, hnk, not_false_eq_true, and_self, ite_true, hg]
            exact le_self_add
        · simp [hb]
      have hcharge := parent_mass_charge lev par mass hbudget
        (fun b => lev b = i ∧ ¬Kept lev par good b)
      apply hsplit.trans
      apply (add_le_add le_rfl (hcharge.trans ih)).trans
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b _
      by_cases hg : good b
      · simp [hg]
      · by_cases hle : lev b ≤ i
        · have hne : lev b ≠ i + 1 := by omega
          simp [hg, hle, hne, show lev b ≤ i + 1 by omega]
        · by_cases heq : lev b = i + 1
          · simp [hg, hle, heq]
          · have hn : ¬lev b ≤ i + 1 := by omega
            simp [hg, hle, heq, hn]
  apply (hstrong i).trans
  apply Finset.sum_le_sum
  intro b _
  by_cases hg : good b
  · simp [hg]
  · by_cases hle : lev b ≤ i <;> simp [hg, hle]

end Submission.Obl.k4_true_forest_own_depth_preparation
