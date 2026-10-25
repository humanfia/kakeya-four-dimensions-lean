-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GraphRowSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphBadPairs
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.FiniteValueSelection

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Dependent random choice in a deterministic averaging form: some large
row has very few pairs with small common-neighbor count. -/
theorem graph_large_row_few_bad_pairs {I J : Type*} [Fintype I] [Nonempty I]
    [Fintype J] [Nonempty J] (R : I → J → Prop) {d : ℝ} (hd : 0 < d)
    (hcol : ∀ j, d * (Fintype.card I : ℝ) ≤ ((Finset.univ.filter (fun i => R i j)).card : ℝ)) :
    ∃ i : I, (d / 2) * (Fintype.card J : ℝ) ≤ ((graphRow R i).card : ℝ) ∧
      ((graphBadPairs R (fun j k => graphCodegree R j k <
        (d ^ 4 / 256) * (Fintype.card I : ℝ)) i).card : ℝ) ≤
          (d ^ 2 / 128) * ((graphRow R i).card : ℝ) ^ 2 := by
  classical
  let N : ℝ := Fintype.card I
  let M : ℝ := Fintype.card J
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hM : 0 < M := by dsimp [M]; exact_mod_cast Fintype.card_pos
  let Bad (j k : J) := graphCodegree R j k < (d ^ 4 / 256) * N
  let b (i : I) : ℝ := (graphBadPairs R Bad i).card
  let D (i : I) : ℝ := (graphRow R i).card
  let coeff := 128 / d ^ 2
  let score (i : I) : ℝ := D i ^ 2 - coeff * b i
  have hc : 0 < coeff := by dsimp [coeff]; positivity
  have hb (i : I) : 0 ≤ b i := Nat.cast_nonneg _
  have hD (i : I) : 0 ≤ D i := Nat.cast_nonneg _
  have hbad : (∑ i, b i) ≤ M ^ 2 * ((d ^ 4 / 256) * N) :=
    graph_bad_pairs_total R Bad (by positivity) (fun j k h => h.le)
  have hsecond : d ^ 2 * N * M ^ 2 ≤ ∑ i, D i ^ 2 := graph_row_second_moment R hd.le hcol
  have hcoef : coeff * (M ^ 2 * ((d ^ 4 / 256) * N)) = (d ^ 2 / 2) * N * M ^ 2 := by
    dsimp [coeff]
    field_simp
    ring
  have hsum : (d ^ 2 / 2) * N * M ^ 2 ≤ ∑ i, score i := by
    have hh := mul_le_mul_of_nonneg_left hbad hc.le
    rw [hcoef] at hh
    simp only [score, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  obtain ⟨i, hi, hmax⟩ := Finset.univ.exists_max_image score Finset.univ_nonempty
  have hsumUpper : (∑ j, score j) ≤ N * score i := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun j hj => hmax j hj)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  have hscore : (d ^ 2 / 2) * M ^ 2 ≤ score i := by
    apply (mul_le_mul_iff_right₀ hN).mp
    have hh := hsum.trans hsumUpper
    convert hh using 1 <;> ring
  have hnonneg : 0 ≤ score i := (by positivity : 0 ≤ (d ^ 2 / 2) * M ^ 2).trans hscore
  have hterm : coeff * b i ≤ D i ^ 2 := by dsimp [score] at hnonneg; linarith
  have hlarge : (d / 2) * M ≤ D i := by
    have hh : 0 ≤ coeff * b i := mul_nonneg hc.le (hb i)
    dsimp [score] at hscore
    nlinarith [hD i]
  have hsmall : b i ≤ (d ^ 2 / 128) * D i ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hterm (sq_nonneg d)
    have hid : d ^ 2 * (coeff * b i) = 128 * b i := by dsimp [coeff]; field_simp
    rw [hid] at hh
    nlinarith
  exact ⟨i, hlarge, hsmall⟩

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
