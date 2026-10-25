-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.MassSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.GlobalPartition
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- Select one of finitely many levels without imposing any uniformity on the weights. -/
lemma weighted_level_selection {α : Type*} [DecidableEq α] (F : Finset α)
    (w : α → ℝ≥0∞) (L : ℕ) (P : α → ℕ → Prop)
    (hP : ∀ Q ∈ F, ∃ j, j ≤ L ∧ P Q j) :
    ∃ j, j ≤ L ∧ ∃ G : Finset α, G ⊆ F ∧
      (∀ Q ∈ G, P Q j) ∧ (∑ Q ∈ F, w Q) ≤ (L + 1 : ℝ≥0∞) * ∑ Q ∈ G, w Q := by
  classical
  have hc (Q : α) : ∃ j : Fin (L + 1), Q ∈ F → P Q j := by
    by_cases hQ : Q ∈ F
    · obtain ⟨j, hj, h⟩ := hP Q hQ
      exact ⟨⟨j, by omega⟩, fun _ => h⟩
    · exact ⟨⟨0, by omega⟩, fun h => (hQ h).elim⟩
  choose c hc using hc
  obtain ⟨j, hj⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color
    (Nat.succ_pos L) F c w
  refine ⟨j, by omega, F.filter (fun Q => c Q = j), Finset.filter_subset _ _, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨hQ, he⟩ := Finset.mem_filter.mp hQ
    simpa only [he] using hc Q hQ
  · simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hj

/-- A disjoint collection of finite classes has the expected additive mass and size. -/
lemma disjoint_class_sum {n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : (F : Set (Finset (Fin n))).PairwiseDisjoint id) (w : Fin n → ℝ≥0∞) :
    (∑ Q ∈ F, ∑ i ∈ Q, w i) = ∑ i ∈ F.biUnion id, w i := by
  classical
  exact (Finset.sum_biUnion hF).symm

lemma disjoint_class_card {n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : (F : Set (Finset (Fin n))).PairwiseDisjoint id) :
    (∑ Q ∈ F, (Q.card : ℝ)) ≤ n := by
  classical
  have he : ∑ Q ∈ F, Q.card = (F.biUnion id).card := (Finset.card_biUnion hF).symm
  have hh : (F.biUnion id).card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card (Finset.subset_univ (F.biUnion id)))
  exact_mod_cast he ▸ hh

/-- Small discarded weight leaves at least half of any prescribed initial mass. -/
lemma retained_class_mass {n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : (F : Set (Finset (Fin n))).PairwiseDisjoint id) (w : Fin n → ℝ≥0∞)
    (hw : ∀ i, w i ≠ ⊤) {M : ℝ≥0∞} (hM : M ≤ ∑ i, w i)
    (hrem : (∑ i ∈ Finset.univ \ F.biUnion id, w i) ≤ M / 2) :
    M ≤ 2 * ∑ Q ∈ F, ∑ i ∈ Q, w i := by
  classical
  have hfinite : (∑ i, w i) ≠ ⊤ := by simpa using hw
  have hMf : M ≠ ⊤ := ne_top_of_le_ne_top hfinite hM
  have he : (∑ i ∈ Finset.univ \ F.biUnion id, w i) +
      (∑ Q ∈ F, ∑ i ∈ Q, w i) = ∑ i, w i := by
    rw [disjoint_class_sum F hF]
    exact Finset.sum_sdiff (Finset.subset_univ _) |>.trans (by rfl)
  have hh : M / 2 ≤ ∑ Q ∈ F, ∑ i ∈ Q, w i := by
    apply ENNReal.le_of_add_le_add_left
      (show M / 2 ≠ ⊤ from ENNReal.div_ne_top hMf (by norm_num))
    calc
      M / 2 + M / 2 = M := ENNReal.add_halves M
      _ ≤ ∑ i, w i := hM
      _ = _ := he.symm
      _ ≤ _ := add_le_add hrem le_rfl
  have ht := mul_le_mul' (le_refl (2 : ℝ≥0∞)) hh
  simpa only [ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)] using ht

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
