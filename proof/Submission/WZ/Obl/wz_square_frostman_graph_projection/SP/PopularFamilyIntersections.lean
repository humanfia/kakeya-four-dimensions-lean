-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.PopularFamilyIntersections.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.FiniteFamilyEnergy
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.FiniteValueSelection

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

/-- A family of large subsets has an anchor with large intersections
with a positive proportion of the whole family. -/
theorem popular_family_intersections {I X : Type*} [Fintype I] [Nonempty I] [DecidableEq X]
    (F : I → Finset X) (S : Finset X) {q : ℝ} (hq : 0 < q) (hS : S.Nonempty)
    (hsub : ∀ i, F i ⊆ S) (hsize : ∀ i, q * (S.card : ℝ) ≤ ((F i).card : ℝ)) :
    ∃ (a : I) (T : Finset I), T.Nonempty ∧
      (q ^ 2 / 2) * (Fintype.card I : ℝ) ≤ (T.card : ℝ) ∧
      ∀ i ∈ T, (q ^ 2 / 2) * (S.card : ℝ) ≤ ((F a ∩ F i).card : ℝ) := by
  classical
  have hN : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hM : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  let f (i : I) : ℝ := ∑ j : I, ((F i ∩ F j).card : ℝ)
  obtain ⟨a, ha, hmax⟩ := Finset.univ.exists_max_image f Finset.univ_nonempty
  have hsum : q * (S.card : ℝ) * (Fintype.card I : ℝ) ≤ ∑ i, ((F i).card : ℝ) := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => hsize i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
    convert hh using 1 <;> ring
  have henergy := finite_family_intersection_energy F S hsub
  have hupper : (∑ i : I, ∑ j : I, ((F i ∩ F j).card : ℝ)) ≤
      (Fintype.card I : ℝ) * f a := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i hi => hmax i hi)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, f] using hh
  have hrow : q ^ 2 * (S.card : ℝ) * (Fintype.card I : ℝ) ≤ f a := by
    have hh := (pow_le_pow_left₀ (by positivity : 0 ≤ q * (S.card : ℝ) * (Fintype.card I : ℝ)) hsum 2).trans
      (henergy.trans (mul_le_mul_of_nonneg_left hupper hN.le))
    apply (mul_le_mul_iff_right₀ (mul_pos hN hM)).mp
    convert hh using 1 <;> ring
  let g (i : I) : ℝ := (F a ∩ F i).card
  have hg (i : I) : 0 ≤ g i ∧ g i ≤ (S.card : ℝ) := by
    constructor
    · exact Nat.cast_nonneg _
    · dsimp only [g]
      exact_mod_cast Finset.card_le_card ((Finset.inter_subset_left).trans (hsub a))
  obtain ⟨T, hTsub, hTsize, hTlarge⟩ := finite_many_large_values (Finset.univ : Finset I) g hN
    (sq_nonneg q) (fun i _ => hg i) (by simpa only [Finset.card_univ, f, g] using hrow)
  simp only [Finset.card_univ] at hTsize
  have hT : T.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < T.card := (mul_pos (by positivity : 0 < q ^ 2 / 2) hM).trans_le hTsize
    exact_mod_cast hh
  exact ⟨a, T, hT, hTsize, hTlarge⟩

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
