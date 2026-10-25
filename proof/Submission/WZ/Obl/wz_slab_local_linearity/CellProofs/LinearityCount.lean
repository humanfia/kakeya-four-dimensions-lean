-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.LinearityCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Counting tools for local linearity (sticky Lemma 5.3)

Cauchy–Schwarz collision counts and pigeonhole bounds over finite sets, used to count the
"paths of length three" (pairs of cells in a common local grain, then quadruples) in the proof
of sticky Lemma 5.3.
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset

/-- The pairs of a finite set with equal key. -/
def keyPairs {α β : Type*} [DecidableEq β] (s : Finset α) (k : α → β) : Finset (α × α) :=
  (s ×ˢ s).filter fun p => k p.1 = k p.2

theorem mem_keyPairs {α β : Type*} [DecidableEq β] {s : Finset α} {k : α → β} {p : α × α} :
    p ∈ keyPairs s k ↔ p.1 ∈ s ∧ p.2 ∈ s ∧ k p.1 = k p.2 := by
  simp [keyPairs, and_assoc]

/-- The number of pairs with equal key is the sum of the squares of the fibre sizes. -/
theorem card_keyPairs {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α) (k : α → β) :
    #(keyPairs s k) = ∑ v ∈ s.image k, #{a ∈ s | k a = v} ^ 2 := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun p : α × α => k p.1) (t := s.image k)]
  · refine sum_congr rfl fun v _ => ?_
    rw [sq, ← card_product]
    congr 1
    ext ⟨a, b⟩
    simp only [keyPairs, mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hv⟩
      exact ⟨⟨ha, hv⟩, hb, hab ▸ hv⟩
    · rintro ⟨⟨ha, hv⟩, hb, hv'⟩
      exact ⟨⟨⟨ha, hb⟩, hv.trans hv'.symm⟩, hv⟩
  · intro p hp
    exact mem_image_of_mem k (mem_keyPairs.mp hp).1

/-- **Collision count** (Cauchy–Schwarz): `#s² ≤ #(image) · #(pairs with equal key)`. -/
theorem card_sq_le_card_image_mul_card_keyPairs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (k : α → β) :
    (#s : ℝ) ^ 2 ≤ (#(s.image k) : ℝ) * #(keyPairs s k) := by
  classical
  have h1 : (#s : ℝ) = ∑ v ∈ s.image k, (#{a ∈ s | k a = v} : ℝ) := by
    rw [card_eq_sum_card_image k s]; push_cast; rfl
  have h2 : (#(keyPairs s k) : ℝ) = ∑ v ∈ s.image k, (#{a ∈ s | k a = v} : ℝ) ^ 2 := by
    rw [card_keyPairs]; push_cast; rfl
  rw [h1, h2]
  exact sq_sum_le_card_mul_sum_sq

/-- Collision count with an upper bound `N` on the number of keys. -/
theorem card_sq_le_mul_card_keyPairs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (k : α → β) {N : ℝ} (hN : (#(s.image k) : ℝ) ≤ N) :
    (#s : ℝ) ^ 2 ≤ N * #(keyPairs s k) := by
  calc (#s : ℝ) ^ 2 ≤ (#(s.image k) : ℝ) * #(keyPairs s k) :=
        card_sq_le_card_image_mul_card_keyPairs s k
    _ ≤ N * #(keyPairs s k) := by gcongr

/-- Pigeonhole with a real bound: some key has a fibre of size at least `#s / N`, when the
keys take at most `N` values. -/
theorem exists_card_fiber_ge {α β : Type*} [DecidableEq β] (s : Finset α) (k : α → β)
    (hs : s.Nonempty) {N : ℝ} (hN : (#(s.image k) : ℝ) ≤ N) :
    ∃ v ∈ s.image k, (#s : ℝ) / N ≤ #{a ∈ s | k a = v} := by
  classical
  have hpos : (0 : ℝ) < #(s.image k) := by
    exact_mod_cast card_pos.mpr (hs.image k)
  have hNpos : 0 < N := lt_of_lt_of_le hpos hN
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hsum : (#s : ℝ) = ∑ v ∈ s.image k, (#{a ∈ s | k a = v} : ℝ) := by
    rw [card_eq_sum_card_image k s]; push_cast; rfl
  have hlt : ∑ v ∈ s.image k, (#{a ∈ s | k a = v} : ℝ) <
      ∑ _v ∈ s.image k, (#s : ℝ) / N :=
    sum_lt_sum_of_nonempty (hs.image k) hcon
  rw [sum_const, nsmul_eq_mul, ← hsum] at hlt
  have : (#(s.image k) : ℝ) * (#s / N) ≤ #s := by
    calc (#(s.image k) : ℝ) * (#s / N) ≤ N * (#s / N) := by gcongr
      _ = #s := by field_simp
  linarith

/-- Number of keys bounded by a covering: if the keys of `s` lie in the image of a function on
`Fin m`, there are at most `m` of them. -/
theorem card_image_le_of_subset_range {α β : Type*} [DecidableEq β] (s : Finset α) (k : α → β)
    {m : ℕ} (c : Fin m → β) (h : ∀ a ∈ s, ∃ j, k a = c j) : #(s.image k) ≤ m := by
  classical
  calc #(s.image k) ≤ #(Finset.univ.image c) := by
        apply card_le_card
        intro v hv
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hv
        obtain ⟨j, hj⟩ := h a ha
        exact mem_image.mpr ⟨j, mem_univ _, hj.symm⟩
    _ ≤ #(Finset.univ : Finset (Fin m)) := card_image_le
    _ = m := by simp

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
