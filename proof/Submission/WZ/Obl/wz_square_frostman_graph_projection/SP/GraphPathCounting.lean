-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GraphPathCounting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphBadPairs

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite incidence counts can be summed from either side. -/
theorem sum_finite_relation_card {I J : Type*} (S : Finset I) (T : Finset J)
    (R : I → J → Prop) :
    (∑ i ∈ S, ((T.filter (R i)).card : ℝ)) =
      ∑ j ∈ T, ((S.filter (fun i => R i j)).card : ℝ) := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Finset.sum_comm

noncomputable def graphThreePaths {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (x : I) (b : J) : Finset (I × J) :=
  Finset.univ.filter (fun p => R x p.2 ∧ R p.1 p.2 ∧ R p.1 b)

/-- Paths of length three are counted by their middle right vertex. -/
theorem graph_three_paths_sum {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (x : I) (b : J) :
    ((graphThreePaths R x b).card : ℝ) = ∑ j ∈ graphRow R x, graphCodegree R b j := by
  simp only [graphThreePaths, graphRow, graphCodegree, Finset.card_eq_sum_ones,
    Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hx : R x j
  · simp only [hx, true_and, ite_true]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [and_comm]
  · simp [hx]

/-- A set of middle vertices with large codegrees gives many length-three paths. -/
theorem graph_three_paths_lower {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (x : I) (b : J) (T : Finset J) {τ : ℝ}
    (hrow : ∀ j ∈ T, R x j) (hcommon : ∀ j ∈ T, τ ≤ graphCodegree R b j) :
    τ * (T.card : ℝ) ≤ ((graphThreePaths R x b).card : ℝ) := by
  rw [graph_three_paths_sum]
  calc
    τ * (T.card : ℝ) = ∑ _j ∈ T, τ := by simp; ring
    _ ≤ ∑ j ∈ T, graphCodegree R b j := Finset.sum_le_sum (fun j hj => hcommon j hj)
    _ ≤ ∑ j ∈ graphRow R x, graphCodegree R b j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow j hj⟩
      · intro j hj hjT
        exact Nat.cast_nonneg _

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
