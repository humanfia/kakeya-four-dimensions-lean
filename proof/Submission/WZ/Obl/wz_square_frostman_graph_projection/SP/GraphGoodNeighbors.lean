-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GraphGoodNeighbors.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.FiniteValueSelection

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- If few ordered pairs are bad, a large subset has uniformly few bad
neighbors in the original set. -/
theorem prune_bad_neighbors {J : Type*} (U : Finset J) (Bad : J → J → Prop) {d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hU : U.Nonempty)
    (hbad : (∑ j ∈ U, ((U.filter (Bad j)).card : ℝ)) ≤
      (d ^ 2 / 128) * (U.card : ℝ) ^ 2) :
    ∃ V : Finset J, V ⊆ U ∧ V.Nonempty ∧ (U.card : ℝ) ≤ 2 * (V.card : ℝ) ∧
      ∀ j ∈ V, ((U.filter (Bad j)).card : ℝ) ≤ (d / 16) * (U.card : ℝ) := by
  classical
  let N : ℝ := U.card
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Finset.card_pos.mpr hU
  let f (j : J) : ℝ := (U.filter (Bad j)).card
  let t := (d / 16) * N
  let L := U.filter (fun j => t ≤ f j)
  let V := U.filter (fun j => f j ≤ t)
  have ht : 0 < t := by dsimp [t]; positivity
  have hlarge : t * (L.card : ℝ) ≤ (d ^ 2 / 128) * N ^ 2 :=
    (finite_large_values_mass U f t (fun j _ => Nat.cast_nonneg _)).trans hbad
  have hL : (L.card : ℝ) ≤ (d / 8) * N := by
    apply (mul_le_mul_iff_right₀ ht).mp
    calc
      t * (L.card : ℝ) ≤ (d ^ 2 / 128) * N ^ 2 := hlarge
      _ = t * ((d / 8) * N) := by dsimp [t]; ring
  have hL' : (L.card : ℝ) ≤ N / 8 := hL.trans (by nlinarith)
  have hsub : U ⊆ V ∪ L := by
    intro j hj
    by_cases hv : f j ≤ t
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, hv⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, (lt_of_not_ge hv).le⟩)
  have hcard : N ≤ (V.card : ℝ) + (L.card : ℝ) := by
    dsimp only [N]
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hVcard : N ≤ 2 * (V.card : ℝ) := by linarith
  have hV : V.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < V.card := by linarith
    exact_mod_cast hh
  exact ⟨V, Finset.filter_subset _ _, hV, hVcard, fun j hj => (Finset.mem_filter.mp hj).2⟩

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
