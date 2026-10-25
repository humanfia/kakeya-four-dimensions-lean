-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Pruning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

lemma incidence_sum {ι κ : Type*} (S : Finset ι) (J : Finset κ) (E : ι → κ → Prop) :
    ∑ i ∈ S, (J.filter (E i)).card = ∑ j ∈ J, (S.filter fun i => E i j).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

lemma weight_class {ι κ : Type*} [Fintype κ] [Nonempty κ]
    (S : Finset ι) (color : ι → κ) (w : ι → ℝ) :
    ∃ c : κ, (∑ i ∈ S, w i) ≤ Fintype.card κ * ∑ i ∈ S.filter (fun i => color i = c), w i := by
  classical
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun c : κ => ∑ i ∈ S.filter (fun i => color i = c), w i) Finset.univ_nonempty
  refine ⟨c, ?_⟩
  calc
    (∑ i ∈ S, w i) = ∑ c : κ, ∑ i ∈ S.filter (fun i => color i = c), w i := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
    _ ≤ ∑ _ : κ, ∑ i ∈ S.filter (fun i => color i = c), w i :=
      Finset.sum_le_sum fun c hc => hmax c hc
    _ = _ := by simp

/-- Delete high-degree vertices and blocks that lost most of their assigned vertices.
Disjoint assignments make this simpler than unrestricted bipartite pruning. -/
theorem prune_assigned {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (J : Finset κ) (P : κ → Finset ι) (E : ι → κ → Prop)
    (hdisj : (↑J : Set κ).PairwiseDisjoint P)
    (hE : ∀ j ∈ J, ∀ i ∈ P j, E i j)
    {L : ℝ} (hL : 0 < L)
    (hcount : ∀ j ∈ J, (((J.biUnion P).filter fun i => E i j).card : ℝ) ≤ L * (P j).card) :
    ∃ (K : Finset κ) (S : Finset ι), K ⊆ J ∧ S ⊆ J.biUnion P ∧
      ((J.biUnion P).card : ℝ) ≤ 2 * S.card ∧
      (∀ i ∈ S, ∃ j ∈ K, E i j) ∧
      (∀ i ∈ S, ((K.filter (E i)).card : ℝ) ≤ 4 * L) ∧
      (∀ j ∈ K, ((P j).card : ℝ) ≤ 2 * (S.filter fun i => E i j).card) := by
  classical
  let D := J.biUnion P
  let bad := D.filter fun i => 4 * L < ((J.filter (E i)).card : ℝ)
  let Q : κ → Finset ι := fun j => P j \ bad
  let K := J.filter fun j => (P j).card ≤ 2 * (Q j).card
  let S := K.biUnion Q
  have hKD : K ⊆ J := Finset.filter_subset _ _
  have hbad : bad ⊆ D := Finset.filter_subset _ _
  have hPJ (j : κ) (hj : j ∈ J) : P j ⊆ D := Finset.subset_biUnion_of_mem P hj
  have hSD : S ⊆ D := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    exact hPJ j (hKD hj) (Finset.sdiff_subset hij)
  have hQdisj : (↑J : Set κ).PairwiseDisjoint Q := by
    intro j hj j' hj' hne
    exact (hdisj hj hj' hne).mono Finset.sdiff_subset Finset.sdiff_subset
  have hlostdisj : (↑J : Set κ).PairwiseDisjoint (fun j => P j ∩ bad) := by
    intro j hj j' hj' hne
    exact (hdisj hj hj' hne).mono Finset.inter_subset_left Finset.inter_subset_left
  have hsumP : (∑ j ∈ J, ((P j).card : ℝ)) = D.card := by
    exact_mod_cast (Finset.card_biUnion hdisj).symm
  have hsumQ : (∑ j ∈ K, ((Q j).card : ℝ)) = S.card := by
    have hh : (↑K : Set κ).PairwiseDisjoint Q := by
      intro j hj j' hj' hne
      exact hQdisj (hKD hj) (hKD hj') hne
    exact_mod_cast (Finset.card_biUnion hh).symm
  have hsumlost : (∑ j ∈ J, ((P j ∩ bad).card : ℝ)) ≤ bad.card := by
    have hu : J.biUnion (fun j => P j ∩ bad) ⊆ bad := by
      intro i hi
      obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_inter.mp hij).2
    exact_mod_cast (Finset.card_biUnion hlostdisj).symm.le.trans (Finset.card_le_card hu)
  have htotal : (∑ i ∈ D, ((J.filter (E i)).card : ℝ)) ≤ L * D.card := by
    have he : (∑ i ∈ D, ((J.filter (E i)).card : ℝ)) =
        ∑ j ∈ J, ((D.filter fun i => E i j).card : ℝ) := by
      exact_mod_cast incidence_sum D J E
    rw [he, ← hsumP, Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => hcount j hj
  have hbadmass : 4 * (bad.card : ℝ) ≤ D.card := by
    have hh : (4 * L) * (bad.card : ℝ) ≤ L * D.card := calc
      (4 * L) * (bad.card : ℝ) = ∑ _i ∈ bad, 4 * L := by simp [mul_comm]
      _ ≤ ∑ i ∈ bad, ((J.filter (E i)).card : ℝ) :=
        Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le
      _ ≤ ∑ i ∈ D, ((J.filter (E i)).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hbad (by intros; positivity)
      _ ≤ L * D.card := htotal
    apply (mul_le_mul_iff_right₀ hL).mp
    nlinarith
  have hpoint (j : κ) (hj : j ∈ J) :
      ((P j).card : ℝ) ≤ (if j ∈ K then ((Q j).card : ℝ) else 0) +
        2 * (P j ∩ bad).card := by
    have he : ((Q j).card : ℝ) + (P j ∩ bad).card = (P j).card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter (P j) bad
    by_cases hjK : j ∈ K
    · rw [if_pos hjK]
      have : (0 : ℝ) ≤ (P j ∩ bad).card := Nat.cast_nonneg _
      linarith
    · rw [if_neg hjK]
      have hlt : 2 * (Q j).card < (P j).card := by
        have : ¬ (P j).card ≤ 2 * (Q j).card := fun h => hjK (Finset.mem_filter.mpr ⟨hj, h⟩)
        omega
      have hr : 2 * ((Q j).card : ℝ) < (P j).card := by exact_mod_cast hlt
      linarith
  have hmass : (D.card : ℝ) ≤ S.card + 2 * bad.card := calc
    (D.card : ℝ) = ∑ j ∈ J, ((P j).card : ℝ) := hsumP.symm
    _ ≤ ∑ j ∈ J, ((if j ∈ K then ((Q j).card : ℝ) else 0) + 2 * (P j ∩ bad).card) :=
      Finset.sum_le_sum hpoint
    _ = (∑ j ∈ K, ((Q j).card : ℝ)) + 2 * ∑ j ∈ J, ((P j ∩ bad).card : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
      congr 2
      ext j
      simp only [Finset.mem_filter]
      exact and_iff_right_of_imp fun hj => hKD hj
    _ ≤ S.card + 2 * bad.card := by rw [hsumQ]; linarith
  refine ⟨K, S, hKD, hSD, by linarith, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    exact ⟨j, hj, hE j (hKD hj) i (Finset.sdiff_subset hij)⟩
  · intro i hi
    have hn : i ∉ bad := by
      obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_sdiff.mp hij).2
    have hdeg : ((J.filter (E i)).card : ℝ) ≤ 4 * L := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hSD hi, lt_of_not_ge hh⟩)
    exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hKD))).trans hdeg
  · intro j hj
    have hc : ((P j).card : ℝ) ≤ 2 * (Q j).card := by
      exact_mod_cast (Finset.mem_filter.mp hj).2
    have hsub : Q j ⊆ S.filter fun i => E i j := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨j, hj, hi⟩,
        hE j (hKD hj) i (Finset.sdiff_subset hi)⟩
    exact hc.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub)) (by norm_num))

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
