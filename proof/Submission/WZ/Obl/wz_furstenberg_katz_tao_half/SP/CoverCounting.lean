-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.CoverCounting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.IndexedGeometry

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric
open scoped BigOperators

theorem card_le_cover_mul_fiber_bound {X Y : Type*} [PseudoMetricSpace Y]
    (T : Finset X) (f : X → Y) {ρ B : ℝ} {m : ℕ} {cc : Fin m → Y}
    (hcover : Covers ρ (f '' (↑T : Set X)) cc)
    (hbound : ∀ j, ((T.filter (fun x => dist (f x) (cc j) ≤ ρ)).card : ℝ) ≤ B) :
    (T.card : ℝ) ≤ (m : ℝ) * B := by
  classical
  let U (j : Fin m) := T.filter (fun x => dist (f x) (cc j) ≤ ρ)
  have hsub : T ⊆ Finset.univ.biUnion U := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover ⟨x, hx, rfl⟩)
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, hj⟩⟩
  have hc : (T.card : ℝ) ≤ ∑ j, ((U j).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hsum : (∑ j : Fin m, ((U j).card : ℝ)) ≤ ∑ _j : Fin m, B :=
    Finset.sum_le_sum (fun j _ => hbound j)
  exact hc.trans (by simpa using hsum)

theorem ClosedFiniteFrostman.card_of_diameter {δ C r : ℝ} {G T : Finset Plane}
    (hG : ClosedFiniteFrostman δ C G) (hTG : T ⊆ G)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hδr : δ ≤ r)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist x y ≤ r) :
    (T.card : ℝ) ≤ C * r * (G.card : ℝ) := by
  classical
  by_cases hT : T.Nonempty
  · obtain ⟨y, hy⟩ := hT
    have hsub : T ⊆ G.filter (fun x => dist x y ≤ r) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨hTG hx, hdiam x hx y hy⟩
    have hc : (T.card : ℝ) ≤ ((G.filter (fun x => dist x y ≤ r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (hG.filter_closedBall y r hδr)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.card_empty, Nat.cast_zero]
    positivity

theorem Covers.neg_image {r : ℝ} {S : Set ℝ} {m : ℕ} {cc : Fin m → ℝ}
    (h : Covers r S cc) : Covers r ((fun x : ℝ => -x) '' S) (fun j => -cc j) := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (h hy)
  exact Set.mem_iUnion.mpr ⟨j, by simpa only [Metric.mem_closedBall, dist_neg_neg] using hj⟩

theorem CoverLower.neg_image {r N : ℝ} {S : Set ℝ} (h : CoverLower r S N) :
    CoverLower r ((fun x : ℝ => -x) '' S) N := by
  intro m cc hc
  have hneg := hc.neg_image
  apply h m (fun j => -cc j)
  simpa only [Set.image_image, neg_neg, Set.image_id'] using hneg

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
