-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CoverPruning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CoverCounts

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file CoverPruning.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization (incidence_sum prune_assigned)

attribute [local instance] Classical.propDecidable

/-- Changing containers preserves a substantial subfamily when incidences in the
old cover have bounded degree and each new container has controlled load. -/
theorem prune_changed_cover {n p : ℕ} (A : Fin n → Set Space)
    (P Q : Fin p → Set Space) {D L : ℝ} (hD : 0 < D) (hL : 0 < L)
    (hcover : ∀ i, ∃ j, A i ⊆ P j)
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D)
    (hpreserve : ∀ i j, A i ⊆ P j → A i ⊆ Q j)
    (hload : ∀ j, (contained A (Q j) : ℝ) ≤ L * contained A (P j)) :
    ∃ (J : Finset (Fin p)) (R : Finset (Fin n)),
      (n : ℝ) ≤ 4 * R.card ∧
      (∀ i ∈ R, ∃ j ∈ J, A i ⊆ Q j) ∧
      (∀ i ∈ R, ((J.filter fun j => A i ⊆ Q j).card : ℝ) ≤ 8 * L * D) ∧
      (∀ j ∈ J, (contained A (P j) : ℝ) ≤
        4 * D * (R.filter fun i => A i ⊆ Q j).card) := by
  classical
  choose f hf using hcover
  let B : Fin p → Finset (Fin n) := fun j => Finset.univ.filter fun i => f i = j
  have hdisj : (univ : Set (Fin p)).PairwiseDisjoint B := by
    intro j hj j' hj' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    exact hne ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hi').2)
  have hBcover : (Finset.univ : Finset (Fin p)).biUnion B = Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, B, Finset.mem_filter]
    exact ⟨fun _ => trivial, fun _ => ⟨f i, rfl⟩⟩
  have hsumB : (∑ j : Fin p, ((B j).card : ℝ)) = n := by
    have hh := Finset.card_biUnion (s := (Finset.univ : Finset (Fin p)))
      (t := B) (by simpa using hdisj)
    rw [hBcover] at hh
    simpa using (congrArg (fun a : ℕ => (a : ℝ)) hh).symm
  have hsumOld : (∑ j : Fin p, (contained A (P j) : ℝ)) ≤ D * n := by
    have hinc : (∑ j : Fin p, (contained A (P j) : ℝ)) =
        ∑ i : Fin n, (ncard {j | A i ⊆ P j} : ℝ) := by
      simp only [contained_eq_card,
        WangZahlLot.Obl.wz_concentrated_convex_factorization.ncard_fintype]
      exact_mod_cast (incidence_sum Finset.univ Finset.univ (fun i j => A i ⊆ P j)).symm
    rw [hinc]
    calc
      _ ≤ ∑ _i : Fin n, D := Finset.sum_le_sum fun i _ => hdegree i
      _ = D * n := by simp [mul_comm]
  let J := Finset.univ.filter fun j => (contained A (P j) : ℝ) ≤ 2 * D * (B j).card
  let bad := Finset.univ \ J
  have hbad : 2 * D * (∑ j ∈ bad, ((B j).card : ℝ)) ≤ D * n := by
    calc
      _ = ∑ j ∈ bad, 2 * D * (B j).card := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ bad, (contained A (P j) : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : ¬ (contained A (P j) : ℝ) ≤ 2 * D * (B j).card := by
          simpa [J] using (Finset.mem_sdiff.mp hj).2
        exact (lt_of_not_ge hj').le
      _ ≤ ∑ j : Fin p, (contained A (P j) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (by intros; positivity)
      _ ≤ D * n := hsumOld
  have hbad' : 2 * (∑ j ∈ bad, ((B j).card : ℝ)) ≤ n := by nlinarith
  have hsplit : (∑ j ∈ J, ((B j).card : ℝ)) +
      (∑ j ∈ bad, ((B j).card : ℝ)) = n := by
    rw [add_comm, Finset.sum_sdiff (Finset.subset_univ _)]
    exact hsumB
  have hJdisj : (↑J : Set (Fin p)).PairwiseDisjoint B := by
    intro j hj j' hj' hne
    exact hdisj (mem_univ _) (mem_univ _) hne
  have hmass : (n : ℝ) ≤ 2 * (J.biUnion B).card := by
    have he : ((J.biUnion B).card : ℝ) = ∑ j ∈ J, ((B j).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion hJdisj
    rw [he]
    linarith
  have hsize (j : Fin p) (hj : j ∈ J) :
      (((J.biUnion B).filter fun i => A i ⊆ Q j).card : ℝ) ≤
        (2 * L * D) * (B j).card := by
    have hs : (J.biUnion B).filter (fun i => A i ⊆ Q j) ⊆
        Finset.univ.filter (fun i => A i ⊆ Q j) :=
      Finset.filter_subset_filter _ (Finset.subset_univ _)
    have hb := (Finset.mem_filter.mp hj).2
    calc
      _ ≤ (contained A (Q j) : ℝ) := by
        rw [contained_eq_card]
        exact Nat.cast_le.mpr (Finset.card_le_card hs)
      _ ≤ L * contained A (P j) := hload j
      _ ≤ L * (2 * D * (B j).card) := mul_le_mul_of_nonneg_left hb hL.le
      _ = _ := by ring
  obtain ⟨K, R, hKJ, hR, hRmass, hRc, hRd, hRcount⟩ :=
    prune_assigned J B (fun i j => A i ⊆ Q j) hJdisj
      (fun j hj i hi => hpreserve i j (by
        have he := (Finset.mem_filter.mp hi).2
        simpa only [he] using hf i))
      (by positivity : 0 < 2 * L * D) hsize
  refine ⟨K, R, by nlinarith, hRc, ?_, ?_⟩
  · intro i hi
    convert hRd i hi using 1 <;> ring
  · intro j hj
    have hb := (Finset.mem_filter.mp (hKJ hj)).2
    have hr := mul_le_mul_of_nonneg_left (hRcount j hj) (by positivity : 0 ≤ 2 * D)
    nlinarith

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
