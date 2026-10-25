-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Blocks.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

noncomputable section

/-- Repeatedly extract a nonempty good block until at least half the original set is covered. -/
theorem disjoint_blocks {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (Good : Finset ι → Prop)
    (select : ∀ R ⊆ S, (S.card : ℝ) ≤ 2 * R.card → R.Nonempty →
      ∃ P : Finset ι, P ⊆ R ∧ P.Nonempty ∧ Good P) :
    ∃ F : Finset (Finset ι),
      (∀ P ∈ F, P.Nonempty ∧ P ⊆ S ∧ Good P) ∧
      (↑F : Set (Finset ι)).PairwiseDisjoint id ∧
      (S.card : ℝ) ≤ 2 * (F.biUnion id).card := by
  classical
  have aux : ∀ m : ℕ, ∀ R : Finset ι, R ⊆ S → R.card = m →
      ∃ F : Finset (Finset ι),
        (∀ P ∈ F, P.Nonempty ∧ P ⊆ R ∧ Good P) ∧
        (↑F : Set (Finset ι)).PairwiseDisjoint id ∧
        (R.card : ℝ) ≤ (S.card : ℝ) / 2 + (F.biUnion id).card := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro R hRS hRm
      by_cases hsmall : (R.card : ℝ) ≤ (S.card : ℝ) / 2
      · refine ⟨∅, by simp, by simp, ?_⟩
        simpa using hsmall
      have hRpos : 0 < R.card := by
        have : (0 : ℝ) < R.card := lt_of_le_of_lt (by positivity) (lt_of_not_ge hsmall)
        exact_mod_cast this
      obtain ⟨P, hPR, hP, hgood⟩ := select R hRS (by linarith) (Finset.card_pos.mp hRpos)
      have hlt : (R \ P).card < m := by
        have hc := Finset.card_sdiff_add_card_eq_card hPR
        have hp := Finset.card_pos.mpr hP
        have hpR := Finset.card_le_card hPR
        omega
      obtain ⟨F, hF, hdisj, hmass⟩ := ih _ hlt (R \ P) ((Finset.sdiff_subset).trans hRS) rfl
      have hUnion : F.biUnion id ⊆ R \ P := by
        intro i hi
        obtain ⟨Q, hQ, hiQ⟩ := Finset.mem_biUnion.mp hi
        exact (hF Q hQ).2.1 hiQ
      have hPU : Disjoint P (F.biUnion id) := by
        apply Finset.disjoint_left.mpr
        intro i hiP hiU
        exact (Finset.mem_sdiff.mp (hUnion hiU)).2 hiP
      have hPQ (Q) (hQ : Q ∈ F) : Disjoint P Q := by
        apply Finset.disjoint_left.mpr
        intro i hiP hiQ
        exact (Finset.mem_sdiff.mp ((hF Q hQ).2.1 hiQ)).2 hiP
      refine ⟨insert P F, ?_, ?_, ?_⟩
      · intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · exact ⟨hP, hPR, hgood⟩
        · exact ⟨(hF Q hQ).1, ((hF Q hQ).2.1).trans Finset.sdiff_subset, (hF Q hQ).2.2⟩
      · intro Q hQ Q' hQ' hne
        change Disjoint Q Q'
        rcases Finset.mem_insert.mp hQ with hQP | hQF <;>
          rcases Finset.mem_insert.mp hQ' with hQ'P | hQ'F
        · exact (hne (hQP.trans hQ'P.symm)).elim
        · simpa only [hQP, id_eq] using hPQ Q' hQ'F
        · simpa only [hQ'P, id_eq] using (hPQ Q hQF).symm
        · exact hdisj hQF hQ'F hne
      · have hcard : (R \ P).card + P.card = R.card := Finset.card_sdiff_add_card_eq_card hPR
        have hu : ((insert P F).biUnion id).card = P.card + (F.biUnion id).card := by
          rw [Finset.biUnion_insert, id_eq, Finset.card_union_of_disjoint hPU]
        rw [hu, Nat.cast_add]
        have hc : ((R \ P).card : ℝ) + P.card = R.card := by exact_mod_cast hcard
        linarith
  obtain ⟨F, hF, hd, hm⟩ := aux S.card S (Finset.Subset.refl _) rfl
  exact ⟨F, hF, hd, by linarith⟩

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
