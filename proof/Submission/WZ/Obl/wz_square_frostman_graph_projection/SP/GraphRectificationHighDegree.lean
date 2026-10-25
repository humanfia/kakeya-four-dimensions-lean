-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GraphRectificationHighDegree.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphRowSelection
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphGoodNeighbors
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphPathCounting

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- A bipartite graph with uniformly large right degrees contains large
left and right sets with many length-three paths between every pair. -/
theorem graph_rectification_high_degree {I J : Type*} [Fintype I] [Nonempty I]
    [Fintype J] [Nonempty J] (R : I → J → Prop) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hcol : ∀ j, d * (Fintype.card I : ℝ) ≤ ((Finset.univ.filter (fun i => R i j)).card : ℝ)) :
    ∃ (X : Finset I) (Y : Finset J), X.Nonempty ∧ Y.Nonempty ∧
      (d / 2) * (Fintype.card I : ℝ) ≤ (X.card : ℝ) ∧
      (d / 4) * (Fintype.card J : ℝ) ≤ (Y.card : ℝ) ∧
      ∀ x ∈ X, ∀ b ∈ Y,
        (d ^ 6 / 4096) * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ≤
          ((graphThreePaths R x b).card : ℝ) := by
  classical
  let N : ℝ := Fintype.card I
  let M : ℝ := Fintype.card J
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hM : 0 < M := by dsimp [M]; exact_mod_cast Fintype.card_pos
  let Bad (j k : J) := graphCodegree R j k < (d ^ 4 / 256) * N
  obtain ⟨i₀, hUsize, hbad⟩ := graph_large_row_few_bad_pairs R hd hcol
  let U := graphRow R i₀
  have hU : U.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < U.card := (mul_pos (by positivity : 0 < d / 2) hM).trans_le hUsize
    exact_mod_cast hh
  have hbad' : (∑ j ∈ U, ((U.filter (Bad j)).card : ℝ)) ≤
      (d ^ 2 / 128) * (U.card : ℝ) ^ 2 := by
    change ((graphBadPairs R Bad i₀).card : ℝ) ≤ _ at hbad
    rw [graph_bad_pairs_row] at hbad
    exact hbad
  obtain ⟨Y, hYU, hY, hU2Y, hYbad⟩ := prune_bad_neighbors U Bad hd hd1 hU hbad'
  have hYp : (0 : ℝ) < Y.card := by exact_mod_cast Finset.card_pos.mpr hY
  have hYsize : (d / 4) * M ≤ (Y.card : ℝ) := by nlinarith
  let f (x : I) : ℝ := (Y.filter (R x)).card
  have hf (x : I) : 0 ≤ f x ∧ f x ≤ (Y.card : ℝ) := by
    constructor
    · exact Nat.cast_nonneg _
    · dsimp [f]
      exact_mod_cast Finset.card_filter_le Y (R x)
  have hysum : d * (Y.card : ℝ) * ((Finset.univ : Finset I).card : ℝ) ≤
      ∑ x : I, f x := by
    have hh := Finset.sum_le_sum (s := Y) (fun j _ => hcol j)
    simp only [Finset.sum_const, nsmul_eq_mul] at hh
    have hswap := sum_finite_relation_card (Finset.univ : Finset I) Y R
    rw [← hswap] at hh
    simp only [Finset.card_univ]
    convert hh using 1 <;> first | rfl | ring
  obtain ⟨X, hXuniv, hXsize, hXrow⟩ := finite_many_large_values (Finset.univ : Finset I) f hYp hd.le
    (fun x _ => hf x) hysum
  simp only [Finset.card_univ] at hXsize
  have hX : X.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < X.card := (mul_pos (by positivity : 0 < d / 2) hN).trans_le hXsize
    exact_mod_cast hh
  refine ⟨X, Y, hX, hY, hXsize, hYsize, ?_⟩
  intro x hx b hb
  let G := Y.filter (fun j => R x j ∧ ¬Bad b j)
  have hGsub : G ⊆ Y := Finset.filter_subset _ _
  have hGgood (j : J) (hj : j ∈ G) : R x j ∧ ¬Bad b j := (Finset.mem_filter.mp hj).2
  have hsub : Y.filter (R x) ⊆ G ∪ U.filter (Bad b) := by
    intro j hj
    have hjY := (Finset.mem_filter.mp hj).1
    have hjR := (Finset.mem_filter.mp hj).2
    by_cases hbad : Bad b j
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hYU hjY, hbad⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjY, hjR, hbad⟩)
  have hcard : f x ≤ (G.card : ℝ) + ((U.filter (Bad b)).card : ℝ) := by
    dsimp only [f]
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hGlow : (d / 8) * (U.card : ℝ) ≤ (G.card : ℝ) := by
    have hrow := hXrow x hx
    have hbadb := hYbad b hb
    have hscaled := mul_le_mul_of_nonneg_left hU2Y hd.le
    nlinarith
  have hcommon (j : J) (hj : j ∈ G) : (d ^ 4 / 256) * N ≤ graphCodegree R b j :=
    le_of_not_gt (hGgood j hj).2
  have hpaths := graph_three_paths_lower R x b G (fun j hj => (hGgood j hj).1) hcommon
  calc
    (d ^ 6 / 4096) * N * M = ((d ^ 4 / 256) * N) * ((d / 8) * ((d / 2) * M)) := by ring
    _ ≤ ((d ^ 4 / 256) * N) * ((d / 8) * (U.card : ℝ)) := by gcongr
    _ ≤ ((d ^ 4 / 256) * N) * (G.card : ℝ) := by gcongr
    _ ≤ _ := hpaths

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
