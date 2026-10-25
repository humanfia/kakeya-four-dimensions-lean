-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.ParentSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BalancedAssignments
import Submission.WZ.Obl.wz_tower_balanced_refinement.Reindex

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open Set
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective exists_enumerate)

/-- Select one fine index for every represented parent. An upper bound on fiber
sizes gives a lower bound for the number of selected parents. -/
lemma select_distinct_parents {n N : ℕ} (hn : 0 < n) (f : Fin n → Fin N) {F : ℝ}
    (hF : ∀ k, (Set.ncard {i | f i = k} : ℝ) ≤ F) :
    ∃ (q : ℕ) (j : Fin q → Fin n), 0 < q ∧ Function.Injective (f ∘ j) ∧
      (n : ℝ) ≤ F * q ∧ (q : ℝ) ≤ n := by
  classical
  let S := Finset.univ.image f
  let g := enumerate S
  have hgmem (k : Fin S.card) : g k ∈ S := enumerate_mem S k
  have hchoose (k : Fin S.card) : ∃ i, f i = g k := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hgmem k)
    exact ⟨i, hi⟩
  choose j hj using hchoose
  have hg : Function.Injective g := enumerate_injective S
  have hcomp : f ∘ j = g := funext hj
  have hSpos : 0 < S.card := by
    apply Finset.card_pos.mpr
    exact ⟨f ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  refine ⟨S.card, j, hSpos, ?_, ?_, ?_⟩
  · rw [hcomp]
    exact hg
  · have hsum : ∑ k ∈ S, (Set.ncard {i | f i = k} : ℝ) = n := by
      have hh : ∑ k, (Set.ncard {i | f i = k} : ℝ) = n := by exact_mod_cast fiber_card_sum f
      rw [← hh]
      apply Finset.sum_subset (Finset.subset_univ S)
      intro k _ hk
      have he : {i | f i = k} = ∅ := by
        ext i
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hi
        exact hk (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
      simp [he]
    rw [← hsum]
    calc
      _ ≤ ∑ _k ∈ S, F := Finset.sum_le_sum fun k _ => hF k
      _ = _ := by simp; ring
  · have hh : S.card ≤ n := by
      exact (Finset.card_image_le (s := Finset.univ) (f := f)).trans_eq (by simp)
    exact_mod_cast hh

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
