-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.LaminarExtraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Finset

/-- A finite laminar family has a disjoint subfamily with the same union. -/
lemma laminar_disjoint_cover {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hlam : ∀ C ∈ F, ∀ D ∈ F, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D) :
    ∃ G ⊆ F, (G : Set (Finset α)).PairwiseDisjoint id ∧
      F.biUnion id = G.biUnion id := by
  classical
  let G := F.filter fun C => ∀ D ∈ F, C ⊆ D → D ⊆ C
  have hGF : G ⊆ F := Finset.filter_subset _ _
  have hcover : ∀ C ∈ F, ∃ D ∈ G, C ⊆ D := by
    intro C hC
    let H := F.filter fun D => C ⊆ D
    have hH : H.Nonempty := ⟨C, by simp [H, hC]⟩
    obtain ⟨D, hD, hmax⟩ := H.exists_max_image Finset.card hH
    have hDF : D ∈ F := (Finset.mem_filter.mp hD).1
    have hCD : C ⊆ D := (Finset.mem_filter.mp hD).2
    refine ⟨D, Finset.mem_filter.mpr ⟨hDF, ?_⟩, hCD⟩
    intro E hE hDE
    have hEH : E ∈ H := Finset.mem_filter.mpr ⟨hE, hCD.trans hDE⟩
    exact (Finset.eq_of_subset_of_card_le hDE (hmax E hEH)).ge
  refine ⟨G, hGF, ?_, ?_⟩
  · intro C hC D hD hne
    rcases hlam C (hGF hC) D (hGF hD) with hCD | hDC | hdisj
    · exact False.elim (hne (Finset.Subset.antisymm hCD
        ((Finset.mem_filter.mp hC).2 D (hGF hD) hCD)))
    · exact False.elim (hne (Finset.Subset.antisymm
        ((Finset.mem_filter.mp hD).2 C (hGF hC) hDC) hDC))
    · exact hdisj
  · apply Finset.Subset.antisymm
    · intro a ha
      obtain ⟨C, hC, haC⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨D, hD, hCD⟩ := hcover C hC
      exact Finset.mem_biUnion.mpr ⟨D, hD, hCD haC⟩
    · exact Finset.biUnion_subset_biUnion_of_subset_left id hGF

/-- Integral selection under laminar cardinality constraints loses no fractional mass.
This is the finite extraction principle behind dyadic Katz--Tao selection. -/
theorem laminar_weighted_extraction {α : Type*} [DecidableEq α]
    (U : Finset α) (F : Finset (Finset α)) (cap : Finset α → ℕ) (w : α → ℝ)
    (hFU : ∀ C ∈ F, C ⊆ U)
    (hlam : ∀ C ∈ F, ∀ D ∈ F, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D)
    (hw : ∀ a ∈ U, 0 ≤ w a ∧ w a ≤ 1)
    (hcap : ∀ C ∈ F, ∑ a ∈ C, w a ≤ cap C) :
    ∃ Q ⊆ U, (∑ a ∈ U, w a) ≤ Q.card ∧
      ∀ C ∈ F, (Q ∩ C).card ≤ cap C := by
  classical
  let A := U.powerset.filter fun Q => ∀ C ∈ F, (Q ∩ C).card ≤ cap C
  have hA : A.Nonempty := ⟨∅, by simp [A]⟩
  obtain ⟨Q, hQ, hmax⟩ := A.exists_max_image Finset.card hA
  have hQU : Q ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hQ).1
  have hQcap : ∀ C ∈ F, (Q ∩ C).card ≤ cap C := (Finset.mem_filter.mp hQ).2
  let S := F.filter fun C => (Q ∩ C).card = cap C
  have hSF : S ⊆ F := Finset.filter_subset _ _
  have hcover : ∀ a ∈ U, a ∉ Q → a ∈ S.biUnion id := by
    intro a ha haQ
    by_contra hn
    have hfeas : insert a Q ∈ A := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset ha hQU), ?_⟩
      intro C hC
      by_cases haC : a ∈ C
      · have hnSat : (Q ∩ C).card ≠ cap C := by
          intro he
          exact hn (Finset.mem_biUnion.mpr
            ⟨C, Finset.mem_filter.mpr ⟨hC, he⟩, haC⟩)
        have hlt := lt_of_le_of_ne (hQcap C hC) hnSat
        rw [Finset.insert_inter_of_mem haC, Finset.card_insert_of_notMem]
        · omega
        · exact fun h => haQ (Finset.mem_inter.mp h).1
      · simpa [Finset.insert_inter_of_notMem haC] using hQcap C hC
    have hc := hmax (insert a Q) hfeas
    rw [Finset.card_insert_of_notMem haQ] at hc
    omega
  obtain ⟨G, hGS, hGdisj, hGcover⟩ := laminar_disjoint_cover S
    (fun C hC D hD => hlam C (hSF hC) D (hSF hD))
  let V := G.biUnion id
  have hVU : V ⊆ U := by
    intro a ha
    obtain ⟨C, hC, haC⟩ := Finset.mem_biUnion.mp ha
    exact hFU C (hSF (hGS hC)) haC
  have hout : U \ V ⊆ Q := by
    intro a ha
    obtain ⟨haU, haV⟩ := Finset.mem_sdiff.mp ha
    by_contra haQ
    exact haV (by change a ∈ G.biUnion id; rw [← hGcover]; exact hcover a haU haQ)
  have hQout : Q \ V = U \ V := by
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_subset_sdiff_left V hQU
    · intro a ha
      exact Finset.mem_sdiff.mpr ⟨hout ha, (Finset.mem_sdiff.mp ha).2⟩
  have hVsum : (∑ a ∈ V, w a) ≤ ((Q ∩ V).card : ℝ) := by
    have hdisj : (G : Set (Finset α)).PairwiseDisjoint (fun C => Q ∩ C) := by
      intro C hC D hD hne
      exact (hGdisj hC hD hne).mono (Finset.inter_subset_right) (Finset.inter_subset_right)
    have hinter : Q ∩ V = G.biUnion (fun C => Q ∩ C) := by
      ext a
      simp only [V, Finset.mem_inter, Finset.mem_biUnion, id_eq]
      aesop
    rw [Finset.sum_biUnion hGdisj, hinter, Finset.card_biUnion hdisj, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro C hC
    rw [(Finset.mem_filter.mp (hGS hC)).2]
    exact hcap C (hSF (hGS hC))
  have houtsum : (∑ a ∈ U \ V, w a) ≤ ((Q \ V).card : ℝ) := by
    rw [hQout]
    calc
      _ ≤ ∑ _a ∈ U \ V, (1 : ℝ) := Finset.sum_le_sum fun a ha =>
        (hw a (Finset.mem_sdiff.mp ha).1).2
      _ = _ := by simp
  refine ⟨Q, hQU, ?_, hQcap⟩
  calc
    (∑ a ∈ U, w a) = (∑ a ∈ U \ V, w a) + ∑ a ∈ V, w a :=
      (Finset.sum_sdiff hVU).symm
    _ ≤ ((Q \ V).card : ℝ) + (Q ∩ V).card := add_le_add houtsum hVsum
    _ = Q.card := by exact_mod_cast Finset.card_sdiff_add_card_inter Q V

/-- Indexed form of laminar extraction; repeated cells may impose different quotas. -/
theorem indexed_laminar_weighted_extraction {α ι : Type*}
    [DecidableEq α] [Fintype ι] (U : Finset α) (C : ι → Finset α)
    (cap : ι → ℕ) (w : α → ℝ)
    (hCU : ∀ i, C i ⊆ U)
    (hlam : ∀ i j, C i ⊆ C j ∨ C j ⊆ C i ∨ Disjoint (C i) (C j))
    (hw : ∀ a ∈ U, 0 ≤ w a ∧ w a ≤ 1)
    (hcap : ∀ i, ∑ a ∈ C i, w a ≤ cap i) :
    ∃ Q ⊆ U, (∑ a ∈ U, w a) ≤ Q.card ∧ ∀ i, (Q ∩ C i).card ≤ cap i := by
  classical
  let F := Finset.univ.image C
  have hex : ∀ D ∈ F, ∃ i, C i = D ∧ ∀ j, C j = D → cap i ≤ cap j := by
    intro D hD
    obtain ⟨i, hi, hCi⟩ := Finset.mem_image.mp hD
    let I := Finset.univ.filter fun j => C j = D
    have hI : I.Nonempty := ⟨i, by simp [I, hCi]⟩
    obtain ⟨j, hj, hmin⟩ := I.exists_min_image cap hI
    refine ⟨j, (Finset.mem_filter.mp hj).2, ?_⟩
    intro k hk
    exact hmin k (by simp [I, hk])
  let m (D : Finset α) := if hD : D ∈ F then cap (hex D hD).choose else 0
  have hm (i : ι) : m (C i) ≤ cap i := by
    have hi : C i ∈ F := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simp only [m, dite_eq_left hi]
    exact (hex (C i) hi).choose_spec.2 i rfl
  have hmweight : ∀ D ∈ F, ∑ a ∈ D, w a ≤ m D := by
    intro D hD
    simp only [m, dite_eq_left hD]
    simpa only [(hex D hD).choose_spec.1] using hcap (hex D hD).choose
  obtain ⟨Q, hQU, hmass, hQcap⟩ := laminar_weighted_extraction U F m w
    (by intro D hD; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hD; exact hCU i)
    (by
      intro D hD E hE
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hD
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hE
      exact hlam i j) hw hmweight
  exact ⟨Q, hQU, hmass, fun i =>
    (hQcap (C i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).trans (hm i)⟩

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
