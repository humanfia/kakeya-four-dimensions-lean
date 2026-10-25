-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalPruning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CoverPruning

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file LocalPruning.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set
open WangZahlLot.Obl.wz_concentrated_convex_factorization (incidence_sum ncard_fintype)

attribute [local instance] Classical.propDecidable

/-- Remove high new-incidence degree and discard old containers that lost more
than half their incidences.  The retained old fibres remain saturated. -/
theorem prune_preserving_old_incidence {n p : ℕ} (A : Fin n → Set Space)
    (P Q : Fin p → Set Space) {D L : ℝ} (hD : 1 ≤ D) (hL : 0 < L)
    (hcover : ∀ i, ∃ j, A i ⊆ P j)
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D)
    (hload : ∀ j, (contained A (Q j) : ℝ) ≤ L * contained A (P j)) :
    ∃ (J : Finset (Fin p)) (R : Finset (Fin n)),
      (n : ℝ) ≤ 2 * R.card ∧
      (∀ i ∈ R, ∃ j ∈ J, A i ⊆ P j) ∧
      (∀ i ∈ R, ((J.filter fun j => A i ⊆ Q j).card : ℝ) ≤ 8 * L * D ^ 2) ∧
      (∀ j ∈ J, (contained A (P j) : ℝ) ≤
        2 * (R.filter fun i => A i ⊆ P j).card) := by
  classical
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let B (j : Fin p) := Finset.univ.filter fun i => A i ⊆ P j
  let deg (i : Fin n) := (Finset.univ.filter fun j => A i ⊆ Q j).card
  let bad := Finset.univ.filter fun i => 8 * L * D ^ 2 < (deg i : ℝ)
  let J := Finset.univ.filter fun j => ((B j).card : ℝ) ≤ 2 * (B j \ bad).card
  let R := (J.biUnion B) \ bad
  have hB (j) : (B j).card = contained A (P j) := by rw [contained_eq_card]
  have hsumOld : (∑ j : Fin p, (contained A (P j) : ℝ)) ≤ D * n := by
    simpa [contained] using cover_incidence_le A P hDpos.le hdegree Set.univ
  have hsumNew : (∑ i : Fin n, (deg i : ℝ)) ≤ L * D * n := by
    calc
      _ = ∑ j : Fin p, (contained A (Q j) : ℝ) := by
        simp only [deg, contained_eq_card]
        exact_mod_cast incidence_sum Finset.univ Finset.univ (fun i j => A i ⊆ Q j)
      _ ≤ ∑ j : Fin p, L * contained A (P j) := Finset.sum_le_sum fun j _ => hload j
      _ = L * ∑ j : Fin p, (contained A (P j) : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ L * (D * n) := mul_le_mul_of_nonneg_left hsumOld hL.le
      _ = _ := by ring
  have hbad : 8 * D * (bad.card : ℝ) ≤ n := by
    have hh : (8 * L * D ^ 2) * (bad.card : ℝ) ≤ L * D * n := by
      calc
        _ = ∑ _i ∈ bad, 8 * L * D ^ 2 := by simp [mul_comm]
        _ ≤ ∑ i ∈ bad, (deg i : ℝ) :=
          Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le
        _ ≤ ∑ i : Fin n, (deg i : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
        _ ≤ _ := hsumNew
    apply (mul_le_mul_iff_left₀ (mul_pos hL hDpos)).mp
    nlinarith only [hh]
  have hfilter (j) : bad.filter (fun i => A i ⊆ P j) = B j ∩ bad := by
    ext i
    simp [B, and_comm]
  have hlost : (∑ j : Fin p, ((B j ∩ bad).card : ℝ)) ≤ D * bad.card := by
    calc
      _ = ∑ j : Fin p, ((bad.filter fun i => A i ⊆ P j).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hfilter j]
      _ = ∑ i ∈ bad, ((Finset.univ.filter fun j => A i ⊆ P j).card : ℝ) := by
        exact_mod_cast (incidence_sum bad Finset.univ (fun i j => A i ⊆ P j)).symm
      _ ≤ ∑ _i ∈ bad, D := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := hdegree i
        rw [ncard_fintype] at hh
        exact hh
      _ = _ := by simp [mul_comm]
  have hdiscard (j) (hj : j ∈ Finset.univ \ J) :
      ((B j).card : ℝ) ≤ 2 * (B j ∩ bad).card := by
    have hnot : ¬ ((B j).card : ℝ) ≤ 2 * (B j \ bad).card := by
      simpa only [J, Finset.mem_filter, Finset.mem_univ, true_and] using (Finset.mem_sdiff.mp hj).2
    have hsplit : ((B j \ bad).card : ℝ) + (B j ∩ bad).card = (B j).card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter (B j) bad
    linarith
  have hdiscardSum : (∑ j ∈ Finset.univ \ J, ((B j).card : ℝ)) ≤ 2 * D * bad.card := by
    calc
      _ ≤ ∑ j ∈ Finset.univ \ J, 2 * ((B j ∩ bad).card : ℝ) := Finset.sum_le_sum hdiscard
      _ = 2 * ∑ j ∈ Finset.univ \ J, ((B j ∩ bad).card : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ∑ j : Fin p, ((B j ∩ bad).card : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (by intros; positivity)) (by norm_num)
      _ ≤ 2 * (D * bad.card) := mul_le_mul_of_nonneg_left hlost (by norm_num)
      _ = _ := by ring
  have hcover' : (Finset.univ : Finset (Fin n)) ⊆ (bad ∪ R) ∪ ((Finset.univ \ J).biUnion B) := by
    intro i hi
    by_cases hibad : i ∈ bad
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hibad)
    · obtain ⟨j, hij⟩ := hcover i
      have hiB : i ∈ B j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
      by_cases hj : j ∈ J
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨j, hj, hiB⟩, hibad⟩))
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩, hiB⟩)
  have hcard : n ≤ bad.card + R.card + ((Finset.univ \ J).biUnion B).card := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ ((bad ∪ R) ∪ ((Finset.univ \ J).biUnion B)).card := Finset.card_le_card hcover'
      _ ≤ (bad ∪ R).card + ((Finset.univ \ J).biUnion B).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hunion : (((Finset.univ \ J).biUnion B).card : ℝ) ≤
      ∑ j ∈ Finset.univ \ J, ((B j).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
  have hmass : (n : ℝ) ≤ 2 * R.card := by
    have hh : (n : ℝ) ≤ (bad.card : ℝ) + R.card + ((Finset.univ \ J).biUnion B).card := by
      exact_mod_cast hcard
    have hbD : (bad.card : ℝ) ≤ D * bad.card := by
      nlinarith [(Nat.cast_nonneg bad.card : (0 : ℝ) ≤ bad.card)]
    nlinarith [(Nat.cast_nonneg R.card : (0 : ℝ) ≤ R.card)]
  refine ⟨J, R, hmass, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hi).1
    exact ⟨j, hj, (Finset.mem_filter.mp hij).2⟩
  · intro i hi
    have hnot := (Finset.mem_sdiff.mp hi).2
    have hdeg : (deg i : ℝ) ≤ 8 * L * D ^ 2 := by
      by_contra hh
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hh⟩)
    exact (Nat.cast_le.mpr (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.subset_univ J)))).trans hdeg
  · intro j hj
    have hjcount := (Finset.mem_filter.mp hj).2
    have hsub : B j \ bad ⊆ R.filter (fun i => A i ⊆ P j) := by
      intro i hi
      obtain ⟨hiB, hibad⟩ := Finset.mem_sdiff.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_biUnion.mpr ⟨j, hj, hiB⟩, hibad⟩, (Finset.mem_filter.mp hiB).2⟩
    rw [← hB j]
    exact hjcount.trans (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (Finset.card_le_card hsub)) (by norm_num))

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
