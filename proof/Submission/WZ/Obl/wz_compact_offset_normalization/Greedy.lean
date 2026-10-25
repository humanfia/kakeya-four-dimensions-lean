-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_compact_offset_normalization.Greedy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Greedy selection in a graph of bounded degree

In a finite family with a symmetric conflict relation of degree at most `M`, a greedy choice
by decreasing weight gives a conflict-free subfamily carrying a `1 / (M + 1)` fraction of the
members and of the total weight.
-/

namespace WangZahlLot.Obl.wz_compact_offset_normalization

open scoped ENNReal

theorem greedy_select {ι : Type*} [DecidableEq ι] (R : ι → ι → Prop) [DecidableRel R]
    (hsymm : ∀ i j, R i j → R j i) (w : ι → ℝ≥0∞) (M : ℕ) :
    ∀ U : Finset ι, (∀ i ∈ U, (U.filter (R i)).card ≤ M) →
    ∃ S ⊆ U, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ R i j) ∧
      U.card ≤ (M + 1) * S.card ∧ ∑ i ∈ U, w i ≤ ((M + 1 : ℕ) : ℝ≥0∞) * ∑ i ∈ S, w i := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
  intro hdeg
  rcases U.eq_empty_or_nonempty with hU | hU
  · exact ⟨∅, by simp [hU], by simp, by simp [hU], by simp [hU]⟩
  obtain ⟨j, hjU, hjmax⟩ := U.exists_max_image w hU
  set U' := U.filter (fun k => k ≠ j ∧ ¬ R j k) with hU'
  have hjU' : j ∉ U' := by simp [hU']
  have hU'U : U' ⊂ U :=
    Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr ⟨j, hjU, hjU'⟩
  have hdeg' : ∀ i ∈ U', (U'.filter (R i)).card ≤ M := fun i hi =>
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans
      (hdeg i (Finset.filter_subset _ _ hi))
  obtain ⟨S', hS'U', hS'pair, hS'card, hS'w⟩ := ih U' hU'U hdeg'
  have hjS' : j ∉ S' := fun h => hjU' (hS'U' h)
  -- the removed part has at most `M + 1` members, each of weight at most `w j`
  set D := U.filter (fun k => ¬ (k ≠ j ∧ ¬ R j k)) with hD
  have hDsub : D ⊆ insert j (U.filter (R j)) := by
    intro k hk
    rw [hD, Finset.mem_filter] at hk
    rw [Finset.mem_insert, Finset.mem_filter]
    by_cases hkj : k = j
    · exact Or.inl hkj
    · right
      refine ⟨hk.1, ?_⟩
      by_contra hR
      exact hk.2 ⟨hkj, hR⟩
  have hDcard : D.card ≤ M + 1 :=
    (Finset.card_le_card hDsub).trans ((Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right (hdeg j hjU) 1))
  have hsplit_card : U'.card + D.card = U.card :=
    Finset.card_filter_add_card_filter_not _
  have hsplit_sum : ∑ i ∈ U', w i + ∑ i ∈ D, w i = ∑ i ∈ U, w i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hDw : ∑ i ∈ D, w i ≤ ((M + 1 : ℕ) : ℝ≥0∞) * w j := by
    calc ∑ i ∈ D, w i ≤ D.card • w j :=
          Finset.sum_le_card_nsmul _ _ _ (fun i hi => hjmax i (Finset.filter_subset _ _ hi))
      _ = (D.card : ℝ≥0∞) * w j := nsmul_eq_mul _ _
      _ ≤ ((M + 1 : ℕ) : ℝ≥0∞) * w j := by gcongr
  refine ⟨insert j S', Finset.insert_subset hjU (hS'U'.trans (Finset.filter_subset _ _)),
    ?_, ?_, ?_⟩
  · intro i hi k hk hik
    rw [Finset.mem_insert] at hi hk
    rcases hi with rfl | hi <;> rcases hk with rfl | hk
    · exact absurd rfl hik
    · have := hS'U' hk
      rw [hU', Finset.mem_filter] at this
      exact this.2.2
    · have := hS'U' hi
      rw [hU', Finset.mem_filter] at this
      exact fun h => this.2.2 (hsymm _ _ h)
    · exact hS'pair i hi k hk hik
  · rw [Finset.card_insert_of_notMem hjS']
    calc U.card = U'.card + D.card := hsplit_card.symm
      _ ≤ (M + 1) * S'.card + (M + 1) := Nat.add_le_add hS'card hDcard
      _ = (M + 1) * (S'.card + 1) := by ring
  · rw [Finset.sum_insert hjS', ← hsplit_sum, mul_add, add_comm (((M + 1 : ℕ) : ℝ≥0∞) * w j)]
    exact add_le_add hS'w hDw

end WangZahlLot.Obl.wz_compact_offset_normalization
