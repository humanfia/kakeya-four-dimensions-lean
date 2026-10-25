-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GraphBadPairs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.NearFarCounting

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products


open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def graphRow {I J : Type*} [Fintype J] (R : I → J → Prop) (i : I) : Finset J :=
  Finset.univ.filter (R i)

noncomputable def graphCodegree {I J : Type*} [Fintype I] (R : I → J → Prop) (j k : J) : ℝ :=
  (Finset.univ.filter (fun i => R i j ∧ R i k)).card

noncomputable def graphBadPairs {I J : Type*} [Fintype J]
    (R : I → J → Prop) (Bad : J → J → Prop) (i : I) : Finset (J × J) :=
  Finset.univ.filter (fun p => R i p.1 ∧ R i p.2 ∧ Bad p.1 p.2)

/-- The total number of bad pairs in rows is at most their common-neighbor
threshold times the total number of possible pairs. -/
theorem graph_bad_pairs_total {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (Bad : J → J → Prop) {T : ℝ} (hT : 0 ≤ T)
    (hbad : ∀ j k, Bad j k → graphCodegree R j k ≤ T) :
    (∑ i, ((graphBadPairs R Bad i).card : ℝ)) ≤ (Fintype.card J : ℝ) ^ 2 * T := by
  classical
  let Rel (i : I) (p : J × J) : Prop := R i p.1 ∧ R i p.2 ∧ Bad p.1 p.2
  have hcol (p : J × J) : ((Finset.univ.filter (fun i => Rel i p)).card : ℝ) ≤ T := by
    by_cases hp : Bad p.1 p.2
    · have hh := hbad p.1 p.2 hp
      simpa only [Rel, hp, and_true, graphCodegree] using hh
    · simp only [Rel, hp, and_false, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
      exact hT
  have hswap : (∑ i, ((graphBadPairs R Bad i).card : ℝ)) =
      ∑ p : J × J, ((Finset.univ.filter (fun i => Rel i p)).card : ℝ) := by
    simpa only [graphBadPairs, Rel, Finset.card_eq_sum_ones, Finset.sum_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using sum_filter_card_comm Rel
  rw [hswap]
  calc
    _ ≤ ∑ _p : J × J, T := Finset.sum_le_sum (fun p _ => hcol p)
    _ = _ := by simp [pow_two]

/-- Counting bad pairs in a row by their first endpoint. -/
theorem graph_bad_pairs_row {I J : Type*} [Fintype J]
    (R : I → J → Prop) (Bad : J → J → Prop) (i : I) :
    ((graphBadPairs R Bad i).card : ℝ) =
      ∑ j ∈ graphRow R i, (((graphRow R i).filter (Bad j)).card : ℝ) := by
  classical
  simp only [graphBadPairs, graphRow, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hr : R i j
  · simp only [hr, true_and, ite_true]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk' : R i k <;> by_cases hbad : Bad j k <;> simp [hk', hbad]
  · simp [hr]

/-- Column degree lower bounds imply a row second-moment lower bound. -/
theorem graph_row_second_moment {I J : Type*} [Fintype I] [Nonempty I] [Fintype J]
    (R : I → J → Prop) {d : ℝ} (hd : 0 ≤ d)
    (hcol : ∀ j, d * (Fintype.card I : ℝ) ≤ ((Finset.univ.filter (fun i => R i j)).card : ℝ)) :
    d ^ 2 * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ^ 2 ≤
      ∑ i, ((graphRow R i).card : ℝ) ^ 2 := by
  classical
  have hN : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hsum : d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ≤
      ∑ i, ((graphRow R i).card : ℝ) := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset J)) (fun j _ => hcol j)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
    have hswap := (sum_filter_card_comm R).symm
    have hs : (∑ j, ((Finset.univ.filter (fun i => R i j)).card : ℝ)) =
        ∑ i, ((graphRow R i).card : ℝ) := by
      simpa only [graphRow, Finset.card_eq_sum_ones, Finset.sum_filter,
        Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hswap
    rw [hs] at hh
    convert hh using 1 <;> ring
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ)) hsum 2
  have hcauchy := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset I))
    (f := fun i => ((graphRow R i).card : ℝ))
  simp only [Finset.card_univ] at hcauchy
  apply (mul_le_mul_iff_right₀ hN).mp
  calc
    (Fintype.card I : ℝ) * (d ^ 2 * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ^ 2) =
        (d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ)) ^ 2 := by ring
    _ ≤ _ := hsq.trans hcauchy

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
