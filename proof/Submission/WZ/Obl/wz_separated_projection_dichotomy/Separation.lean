-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.Separation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Frostman

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem FiniteFrostman.close_pairs {δ C r : ℝ} {T : Finset Plane}
    (h : FiniteFrostman δ C T) (hδr : δ ≤ r) :
    (((T ×ˢ T).filter (fun p => dist p.1 p.2 < r)).card : ℝ) ≤
      C * r * (T.card : ℝ) ^ 2 := by
  have hcard : ((T ×ˢ T).filter (fun p => dist p.1 p.2 < r)).card =
      ∑ b ∈ T, ballCount T b r := by
    simp only [Finset.card_filter, Finset.sum_product, ballCount, Metric.mem_ball, dist_comm]
  rw [hcard, Nat.cast_sum]
  calc ∑ b ∈ T, (ballCount T b r : ℝ) ≤ ∑ _ ∈ T, C * r * (T.card : ℝ) :=
      Finset.sum_le_sum (fun b _ => h b r hδr)
    _ = C * r * (T.card : ℝ) ^ 2 := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Removing triples near either degeneracy locus costs at most the displayed
Frostman bound. No regularity of the hypergraph is needed. -/
theorem separated_triple_refinement {δ C r : ℝ} {S T : Finset Plane}
    (hS : FiniteFrostman δ C S) (hT : FiniteFrostman δ C T) (hδr : δ ≤ r)
    (H : Finset Triple) (hH : H ⊆ S ×ˢ (T ×ˢ T)) :
    ∃ K ⊆ H, (H.card : ℝ) - 2 * C * r * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤
        (K.card : ℝ) ∧
      ∀ p ∈ K, r ≤ ‖p.1‖ ∧ r ≤ dist p.2.1 p.2.2 := by
  classical
  let good (p : Triple) := r ≤ ‖p.1‖ ∧ r ≤ dist p.2.1 p.2.2
  let K := H.filter good
  let B₁ := (S.filter (fun a => ‖a‖ < r)) ×ˢ (T ×ˢ T)
  let B₂ := S ×ˢ ((T ×ˢ T).filter (fun p => dist p.1 p.2 < r))
  have hB₁ : (B₁.card : ℝ) ≤ C * r * (S.card : ℝ) * (T.card : ℝ) ^ 2 := by
    have hcount := hS 0 r hδr
    have hc : (B₁.card : ℝ) = (ballCount S 0 r : ℝ) * (T.card : ℝ) ^ 2 := by
      simp only [B₁, Finset.card_product, Nat.cast_mul, ballCount, Metric.mem_ball,
        dist_zero_right, sq]
    rw [hc]
    exact mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
  have hB₂ : (B₂.card : ℝ) ≤ C * r * (S.card : ℝ) * (T.card : ℝ) ^ 2 := by
    have hcount := hT.close_pairs hδr
    calc (B₂.card : ℝ) = (S.card : ℝ) *
          (((T ×ˢ T).filter (fun p => dist p.1 p.2 < r)).card : ℝ) := by
            simp only [B₂, Finset.card_product, Nat.cast_mul]
      _ ≤ (S.card : ℝ) * (C * r * (T.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg _)
      _ = _ := by ring
  have hbad : H.filter (fun p => ¬ good p) ⊆ B₁ ∪ B₂ := by
    intro p hp
    obtain ⟨hpH, hpbad⟩ := Finset.mem_filter.mp hp
    have hpST := Finset.mem_product.mp (hH hpH)
    by_cases ha : r ≤ ‖p.1‖
    · apply Finset.mem_union_right
      apply Finset.mem_product.mpr
      refine ⟨hpST.1, Finset.mem_filter.mpr ⟨hpST.2, ?_⟩⟩
      exact lt_of_not_ge (fun hb => hpbad ⟨ha, hb⟩)
    · apply Finset.mem_union_left
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hpST.1, lt_of_not_ge ha⟩, hpST.2⟩
  have hbadcard : ((H.filter (fun p => ¬ good p)).card : ℝ) ≤
      (B₁.card : ℝ) + (B₂.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hbad).trans (Finset.card_union_le _ _)
  have hpartition : (K.card : ℝ) + ((H.filter (fun p => ¬ good p)).card : ℝ) =
      (H.card : ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := H) good
  refine ⟨K, Finset.filter_subset _ _, ?_, ?_⟩
  · nlinarith
  · intro p hp
    exact (Finset.mem_filter.mp hp).2

theorem half_separated_triple_refinement {δ C r : ℝ} {S T : Finset Plane}
    (hS : FiniteFrostman δ C S) (hT : FiniteFrostman δ C T) (hδr : δ ≤ r)
    (H : Finset Triple) (hH : H ⊆ S ×ˢ (T ×ˢ T))
    (hsmall : 4 * C * r * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤ (H.card : ℝ)) :
    ∃ K ⊆ H, (H.card : ℝ) / 2 ≤ (K.card : ℝ) ∧
      ∀ p ∈ K, r ≤ ‖p.1‖ ∧ r ≤ dist p.2.1 p.2.2 := by
  obtain ⟨K, hKH, hcard, hsep⟩ := separated_triple_refinement hS hT hδr H hH
  exact ⟨K, hKH, by nlinarith, hsep⟩

end WangZahlLot.Obl.wz_separated_projection_dichotomy
