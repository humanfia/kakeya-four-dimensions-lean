-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.CommonNeighbors.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.Basic

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The total number of common neighbors is the second moment of degrees. -/
theorem common_neighbor_identity {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) :
    (∑ j : J, ((Finset.univ.filter (fun i : I => R i j)).card : ℝ) ^ 2) =
      ∑ i : I, ∑ i' : I, ((Finset.univ.filter (fun j : J => R i j ∧ R i' j)).card : ℝ) := by
  classical
  have hind (i i' : I) (j : J) :
      (if R i j then (1 : ℝ) else 0) * (if R i' j then (1 : ℝ) else 0) =
      if R i j ∧ R i' j then 1 else 0 := by split_ifs <;> simp_all
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, pow_two, Finset.sum_mul_sum, hind]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

theorem sum_relation_degree {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) :
    (∑ j : J, ((Finset.univ.filter (fun i : I => R i j)).card : ℝ)) =
      ((Finset.univ.filter (fun p : I × J => R p.1 p.2)).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- A graph of density `d` has at least a `d^2` fraction of triples with
two edges sharing their right endpoint. -/
theorem dense_relation_common_neighbors {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty J] (R : I → J → Prop) {d : ℝ} (hd : 0 ≤ d)
    (hdensity : d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ≤
      ((Finset.univ.filter (fun p : I × J => R p.1 p.2)).card : ℝ)) :
    d ^ 2 * (Fintype.card I : ℝ) ^ 2 * (Fintype.card J : ℝ) ≤
      ∑ i : I, ∑ i' : I, ((Finset.univ.filter (fun j : J => R i j ∧ R i' j)).card : ℝ) := by
  have hJpos : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hcauchy := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset J))
    (f := fun j => ((Finset.univ.filter (fun i : I => R i j)).card : ℝ))
  rw [sum_relation_degree R, common_neighbor_identity R] at hcauchy
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ d *
    (Fintype.card I : ℝ) * (Fintype.card J : ℝ)) hdensity 2
  apply (mul_le_mul_iff_right₀ hJpos).mp
  calc (Fintype.card J : ℝ) * (d ^ 2 * (Fintype.card I : ℝ) ^ 2 * (Fintype.card J : ℝ)) =
        (d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ)) ^ 2 := by ring
    _ ≤ ((Finset.univ.filter (fun p : I × J => R p.1 p.2)).card : ℝ) ^ 2 := hsquare
    _ ≤ _ := by simpa only [Finset.card_univ] using hcauchy

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
