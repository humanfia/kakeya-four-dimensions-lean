-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.SparseCommonNeighbors.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.CommonNeighbors

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- If most pairs of left vertices have few common neighbors, the relation
itself has small density. The exceptional pairs are controlled row by row. -/
theorem relation_density_sq_bound {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (R : I → J → Prop) (Near : I → I → Prop)
    {a b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hnear : ∀ i, ((Finset.univ.filter (fun i' => Near i i')).card : ℝ) ≤ a * (Fintype.card I : ℝ))
    (hfar : ∀ i i', ¬Near i i' →
      ((Finset.univ.filter (fun j => R i j ∧ R i' j)).card : ℝ) ≤ b * (Fintype.card J : ℝ))
    (hdensity : d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ≤
      ((Finset.univ.filter (fun p : I × J => R p.1 p.2)).card : ℝ)) :
    d ^ 2 ≤ a + b := by
  classical
  let N (i i' : I) : ℝ := (Finset.univ.filter (fun j => R i j ∧ R i' j)).card
  have hcap (i i' : I) : N i i' ≤ (Fintype.card J : ℝ) := by
    dsimp [N]
    exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset J)
      (fun j => R i j ∧ R i' j)).trans_eq Finset.card_univ
  have hrow (i : I) : (∑ i', N i i') ≤ (a + b) * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) := by
    have hsum : (∑ i' : I, if Near i i' then (Fintype.card J : ℝ) else 0) =
        ((Finset.univ.filter (fun i' => Near i i')).card : ℝ) * (Fintype.card J : ℝ) := by
      rw [← Finset.sum_filter]
      simp
    calc (∑ i', N i i') ≤
          ∑ i' : I, ((if Near i i' then (Fintype.card J : ℝ) else 0) + b * (Fintype.card J : ℝ)) := by
          apply Finset.sum_le_sum
          intro i' hi'
          by_cases h : Near i i'
          · rw [if_pos h]
            exact (hcap i i').trans (le_add_of_nonneg_right (by positivity))
          · rw [if_neg h, zero_add]
            exact hfar i i' h
      _ = ((Finset.univ.filter (fun i' => Near i i')).card : ℝ) * (Fintype.card J : ℝ) +
          (Fintype.card I : ℝ) * (b * (Fintype.card J : ℝ)) := by
        rw [Finset.sum_add_distrib, hsum]
        simp
      _ ≤ (a * (Fintype.card I : ℝ)) * (Fintype.card J : ℝ) +
          (Fintype.card I : ℝ) * (b * (Fintype.card J : ℝ)) := by gcongr; exact hnear i
      _ = _ := by ring
  have hupper : (∑ i, ∑ i', N i i') ≤ (a + b) * (Fintype.card I : ℝ) ^ 2 * (Fintype.card J : ℝ) := by
    calc (∑ i, ∑ i', N i i') ≤ ∑ _i : I, (a + b) * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) :=
        Finset.sum_le_sum (fun i hi => hrow i)
      _ = _ := by simp; ring
  have hlower := dense_relation_common_neighbors R hd hdensity
  have hpos : 0 < (Fintype.card I : ℝ) ^ 2 * (Fintype.card J : ℝ) := by
    have hi : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have hj : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
    positivity
  apply (mul_le_mul_iff_left₀ hpos).mp
  nlinarith only [hlower.trans hupper]

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
