-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.PopularRectangles.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.PopularFamilyIntersections

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- Rectangles of positive density have an anchor with large overlaps in
both coordinates for a positive proportion of their indices. -/
theorem popular_rectangles {I α β : Type*} [Fintype I] [Nonempty I]
    [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (X : I → Finset α) (Y : I → Finset β)
    {e : ℝ} (he : 0 < e) (hA : A.Nonempty) (hB : B.Nonempty)
    (hXA : ∀ i, X i ⊆ A) (hYB : ∀ i, Y i ⊆ B)
    (hX : ∀ i, e * (A.card : ℝ) ≤ ((X i).card : ℝ))
    (hY : ∀ i, e * (B.card : ℝ) ≤ ((Y i).card : ℝ)) :
    ∃ (a : I) (T : Finset I), T.Nonempty ∧
      (e ^ 4 / 2) * (Fintype.card I : ℝ) ≤ (T.card : ℝ) ∧
      ∀ i ∈ T,
        (e ^ 4 / 2) * (A.card : ℝ) ≤ ((X a ∩ X i).card : ℝ) ∧
        (e ^ 4 / 2) * (B.card : ℝ) ≤ ((Y a ∩ Y i).card : ℝ) := by
  classical
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  let F (i : I) := X i ×ˢ Y i
  have hsub (i : I) : F i ⊆ A ×ˢ B := by
    intro p hp
    exact Finset.mem_product.mpr ⟨hXA i (Finset.mem_product.mp hp).1,
      hYB i (Finset.mem_product.mp hp).2⟩
  have hsize (i : I) : e ^ 2 * ((A ×ˢ B).card : ℝ) ≤ ((F i).card : ℝ) := by
    simp only [F, Finset.card_product, Nat.cast_mul]
    have hh := mul_le_mul (hX i) (hY i) (by positivity) (Nat.cast_nonneg _)
    convert hh using 1 <;> ring
  obtain ⟨a, T, hT, hTsize, hTlarge⟩ := popular_family_intersections F (A ×ˢ B)
    (by positivity : 0 < e ^ 2) (hA.product hB) hsub hsize
  have heid : (e ^ 2) ^ 2 / 2 = e ^ 4 / 2 := by ring
  rw [heid] at hTsize hTlarge
  refine ⟨a, T, hT, hTsize, ?_⟩
  intro i hi
  have hident : F a ∩ F i = (X a ∩ X i) ×ˢ (Y a ∩ Y i) := by
    ext p
    simp only [F, Finset.mem_inter, Finset.mem_product]
    tauto
  have hp := hTlarge i hi
  rw [hident, Finset.card_product, Finset.card_product] at hp
  push_cast at hp
  have hU : (((X a ∩ X i).card : ℕ) : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card ((Finset.inter_subset_left).trans (hXA a))
  have hV : (((Y a ∩ Y i).card : ℕ) : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast Finset.card_le_card ((Finset.inter_subset_left).trans (hYB a))
  constructor
  · apply (mul_le_mul_iff_left₀ hBp).mp
    have hh := hp.trans (mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _))
    convert hh using 1 <;> ring
  · apply (mul_le_mul_iff_left₀ hAp).mp
    have hh := hp.trans (mul_le_mul_of_nonneg_right hU (Nat.cast_nonneg _))
    convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
