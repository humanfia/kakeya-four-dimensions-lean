-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.OrderedWeightedSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

/-- A symmetric dense weighted graph has a vertex with many popular
neighbors no larger than it in any prescribed real ordering. -/
theorem ordered_weighted_selection {I : Type*} [Fintype I] [Nonempty I]
    (a : I → ℝ) (w : I → I → ℝ) {E : ℝ} (hE : 0 < E)
    (hw : ∀ i j, 0 ≤ w i j) (hsymm : ∀ i j, w i j = w j i)
    (hcap : ∀ i j, w i j ≤ (Fintype.card I : ℝ))
    (henergy : E * (Fintype.card I : ℝ) ^ 3 ≤ ∑ i, ∑ j, w i j) :
    ∃ i : I, ∃ T : Finset I,
      (E / 4) * (Fintype.card I : ℝ) ≤ (T.card : ℝ) ∧
      ∀ j ∈ T, a j ≤ a i ∧ (E / 4) * (Fintype.card I : ℝ) ≤ w i j := by
  classical
  let N : ℝ := Fintype.card I
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  let F (i j : I) : ℝ := if a j ≤ a i then w i j else 0
  let row (i : I) : ℝ := ∑ j, F i j
  have hpair (i j : I) : w i j ≤ F i j + F j i := by
    dsimp [F]
    by_cases hji : a j ≤ a i
    · rw [if_pos hji]
      exact le_add_of_nonneg_right (by split_ifs; exact hw j i; exact le_rfl)
    · rw [if_neg hji, if_pos (le_of_not_ge hji), zero_add, hsymm]
  have htotal : (∑ i, ∑ j, w i j) ≤ 2 * ∑ i, row i := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset I))
      (fun i _ => Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun j _ => hpair i j))
    simp only [Finset.sum_add_distrib] at hh
    have hswap : (∑ i : I, ∑ j : I, F j i) = ∑ i : I, ∑ j : I, F i j := Finset.sum_comm
    rw [hswap] at hh
    dsimp [row]
    linarith
  obtain ⟨i, hi, hmax⟩ := Finset.univ.exists_max_image row Finset.univ_nonempty
  have hrows : (∑ j, row j) ≤ N * row i := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun j hj => hmax j hj)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  have hlarge : (E / 2) * N ^ 2 ≤ row i := by
    apply (mul_le_mul_iff_right₀ hN).mp
    have hh : E * N ^ 3 ≤ 2 * (N * row i) := by
      exact henergy.trans (htotal.trans (mul_le_mul_of_nonneg_left hrows (by norm_num)))
    nlinarith
  let T := Finset.univ.filter (fun j : I => a j ≤ a i ∧ (E / 4) * N ≤ w i j)
  have hT (j : I) (hj : j ∈ T) : a j ≤ a i ∧ (E / 4) * N ≤ w i j := (Finset.mem_filter.mp hj).2
  have hterm (j : I) : F i j ≤ (if j ∈ T then N else 0) + (E / 4) * N := by
    by_cases hj : j ∈ T
    · rw [if_pos hj]
      have hh : F i j = w i j := if_pos (hT j hj).1
      rw [hh]
      exact (hcap i j).trans (le_add_of_nonneg_right (by positivity))
    · rw [if_neg hj, zero_add]
      by_cases hji : a j ≤ a i
      · have hnot : ¬ (E / 4) * N ≤ w i j := by
          intro hh
          exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, hh⟩)
        exact (show F i j = w i j from if_pos hji) ▸ (lt_of_not_ge hnot).le
      · rw [show F i j = 0 from if_neg hji]
        positivity
  have hrowupper : row i ≤ N * (T.card : ℝ) + (E / 4) * N ^ 2 := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun j _ => hterm j)
    rw [Finset.sum_add_distrib] at hh
    have hind : (∑ j : I, if j ∈ T then N else 0) = (T.card : ℝ) * N := by
      rw [← Finset.sum_filter]
      simp
    rw [hind] at hh
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
    dsimp [row]
    dsimp [N] at hh ⊢
    nlinarith
  refine ⟨i, T, ?_, hT⟩
  apply (mul_le_mul_iff_right₀ hN).mp
  nlinarith

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
