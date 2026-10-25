-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_separated_full_subtree.Counting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_separated_full_subtree.Geometry

namespace WangZahlLot.Obl.wz_nsp_separated_full_subtree

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

abbrev ConvexCount (δ L : ℝ) {m : ℕ} (x v : Fin m → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal ((ncard {s | Tube δ (x s) (v s) ⊆ W} : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal L * volume W

/-- Full, disjoint assigned fibers turn the fine convex count into a degree bound
for the conflict graph of a parent layer. -/
theorem near_card_bound {δ r L c : ℝ} {m k : ℕ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hc : 0 < c)
    (x v : Fin m → Space) (z w : Fin k → Space) (f : Fin m → Fin k)
    (hw : ∀ i, ‖w i‖ = 1)
    (hcount : ConvexCount δ L x v)
    (hcontain : ∀ s, Tube δ (x s) (v s) ⊆ Tube r (z (f s)) (w (f s)))
    (hfull : ∀ i, c * r ^ 2 ≤ (ncard {s | f s = i} : ℝ) * δ ^ 2)
    (j : Fin k) :
    ((Finset.univ.filter (fun i => Near r (z j) (w j) (z i) (w i))).card : ℝ) ≤
      200000000000000000000 * L / c := by
  classical
  let N := Finset.univ.filter (fun i => Near r (z j) (w j) (z i) (w i))
  let W := Wide r (z j) (w j)
  have hsub : ∀ s, f s ∈ N → Tube δ (x s) (v s) ⊆ W := by
    intro s hs
    exact (hcontain s).trans (near_subset_wide hr (Finset.mem_filter.mp hs).2)
  have hsum : (∑ i ∈ N, (ncard {s : Fin m | f s = i} : ℝ)) =
      ((Finset.univ.filter (fun s => f s ∈ N)).card : ℝ) := by
    simp_rw [WangZahlLot.Obl.wz_separated_cover_refinement.ncard_setOf]
    exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m)) N f
  have hcard : ((Finset.univ.filter (fun s => f s ∈ N)).card : ℝ) ≤
      (ncard {s | Tube δ (x s) (v s) ⊆ W} : ℝ) := by
    rw [WangZahlLot.Obl.wz_separated_cover_refinement.ncard_setOf]
    exact_mod_cast Finset.card_le_card (show
      Finset.univ.filter (fun s => f s ∈ N) ⊆
        Finset.univ.filter (fun s => Tube δ (x s) (v s) ⊆ W) from
      fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub s (Finset.mem_filter.mp hs).2⟩)
  have hraw : (N.card : ℝ) * c * r ^ 2 ≤
      (ncard {s | Tube δ (x s) (v s) ⊆ W} : ℝ) * δ ^ 2 := by
    calc
      (N.card : ℝ) * c * r ^ 2 = ∑ _i ∈ N, c * r ^ 2 := by simp [mul_assoc]
      _ ≤ ∑ i ∈ N, (ncard {s | f s = i} : ℝ) * δ ^ 2 :=
        Finset.sum_le_sum fun i _ => hfull i
      _ = ((Finset.univ.filter (fun s => f s ∈ N)).card : ℝ) * δ ^ 2 := by
        rw [← Finset.sum_mul, hsum]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg δ)
  have hE : ENNReal.ofReal ((N.card : ℝ) * c * r ^ 2) ≤
      ENNReal.ofReal (L * (200000000000000000000 * r ^ 2)) := by
    calc
      _ ≤ ENNReal.ofReal ((ncard {s | Tube δ (x s) (v s) ⊆ W} : ℝ) * δ ^ 2) :=
        ENNReal.ofReal_le_ofReal hraw
      _ ≤ ENNReal.ofReal L * volume W := hcount W (wide_convex _ _ _)
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal (200000000000000000000 * r ^ 2) :=
        mul_le_mul' le_rfl (wide_volume hr hr1 _ _ (hw j))
      _ = _ := (ENNReal.ofReal_mul hL).symm
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hE
  have hc' : (N.card : ℝ) * c ≤ 200000000000000000000 * L := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hr)).mp
    nlinarith only [hreal]
  exact (le_div_iff₀ hc).mpr hc'

/-- One palette suffices for each layer whose fullness lower bound is `c`. -/
theorem layer_coloring {δ r L c : ℝ} {m k q : ℕ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hL : 0 ≤ L) (hc : 0 < c)
    (hq : 0 < q) (hqbound : 200000000000000000000 * L / c < (q : ℝ))
    (x v : Fin m → Space) (z w : Fin k → Space) (f : Fin m → Fin k)
    (hw : ∀ i, ‖w i‖ = 1) (hcount : ConvexCount δ L x v)
    (hcontain : ∀ s, Tube δ (x s) (v s) ⊆ Tube r (z (f s)) (w (f s)))
    (hfull : ∀ i, c * r ^ 2 ≤ (ncard {s | f s = i} : ℝ) * δ ^ 2) :
    ∃ color : Fin k → Fin q, ∀ i j, i ≠ j → Near r (z i) (w i) (z j) (w j) →
      color i ≠ color j := by
  classical
  apply WangZahlLot.Obl.wz_separated_cover_refinement.color_relation hq
    (fun i j => Near r (z i) (w i) (z j) (w j))
  · exact fun h => near_symm h
  · intro j
    exact_mod_cast (near_card_bound hr hr1 hL hc x v z w f hw hcount hcontain hfull j).trans_lt hqbound

end WangZahlLot.Obl.wz_nsp_separated_full_subtree
