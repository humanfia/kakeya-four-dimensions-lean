-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.NearFarCounting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.CommonNeighbors

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Count a finite relation in either order. -/
theorem sum_filter_card_comm {I J : Type*} [Fintype I] [Fintype J] (R : I → J → Prop) :
    (∑ i, ((Finset.univ.filter (R i)).card : ℝ)) =
      ∑ j, ((Finset.univ.filter (fun i => R i j)).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Finset.sum_comm

/-- Counting a relation on a product is equivalent to summing its fiber sizes. -/
theorem product_filter_card_eq_sum {I J : Type*} [Fintype I] [Fintype J] (R : I → J → Prop) :
    ((Finset.univ.filter (fun p : I × J => R p.1 p.2)).card : ℝ) =
      ∑ i, ((Finset.univ.filter (R i)).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]

/-- Bound the near part row by row and the far part column by column. -/
theorem relation_count_near_far {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (Near : J → Prop) {B T : ℝ} (hT : 0 ≤ T)
    (hnear : ∀ i, ((Finset.univ.filter (fun j => R i j ∧ Near j)).card : ℝ) ≤ B)
    (hfar : ∀ j, ¬Near j → ((Finset.univ.filter (fun i => R i j)).card : ℝ) ≤ T) :
    (∑ i, ((Finset.univ.filter (R i)).card : ℝ)) ≤
      (Fintype.card I : ℝ) * B + (Fintype.card J : ℝ) * T := by
  classical
  have hrow (i : I) : ((Finset.univ.filter (R i)).card : ℝ) ≤
      B + ((Finset.univ.filter (fun j => R i j ∧ ¬Near j)).card : ℝ) := by
    have hsub : Finset.univ.filter (R i) ⊆
        Finset.univ.filter (fun j => R i j ∧ Near j) ∪
          Finset.univ.filter (fun j => R i j ∧ ¬Near j) := by
      intro j hj
      have hij := (Finset.mem_filter.mp hj).2
      by_cases hn : Near j
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hn⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hn⟩)
    have hc : ((Finset.univ.filter (R i)).card : ℝ) ≤
        ((Finset.univ.filter (fun j => R i j ∧ Near j)).card : ℝ) +
          ((Finset.univ.filter (fun j => R i j ∧ ¬Near j)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact hc.trans (add_le_add (hnear i) le_rfl)
  have hcolumn (j : J) : ((Finset.univ.filter (fun i => R i j ∧ ¬Near j)).card : ℝ) ≤ T := by
    by_cases hn : Near j
    · simp only [hn, not_true_eq_false, and_false, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
      exact hT
    · simpa only [hn, not_false_eq_true, and_true] using hfar j hn
  calc
    (∑ i, ((Finset.univ.filter (R i)).card : ℝ)) ≤
        ∑ i, (B + ((Finset.univ.filter (fun j => R i j ∧ ¬Near j)).card : ℝ)) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (Fintype.card I : ℝ) * B +
        ∑ j, ((Finset.univ.filter (fun i => R i j ∧ ¬Near j)).card : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact Finset.sum_comm
    _ ≤ (Fintype.card I : ℝ) * B + ∑ _j : J, T :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hcolumn j))
    _ = _ := by simp

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
