/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file BoundaryPaletteLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.PaletteListCount

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

/-- Fine velocity bins crossing coarse-bin endpoints are charged by their
column counts. Only bins contained in the coarse bin enter the original
palette sum. -/
theorem palette_weighted_list_count_with_boundary
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (states : Finset A) (interior boundary : Finset V) (weight : V → ℝ)
    (compatible : A → V → Prop) [DecidableRel compatible]
    {P C K : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hw : ∀ j ∈ interior, 0 ≤ weight j)
    (hmass : ∑ j ∈ interior, weight j ≤ P)
    (hrow : ∀ a ∈ states, (∀ j ∈ boundary, ¬ compatible a j) →
      P ≤ C * ∑ j ∈ Finset.bipartiteAbove compatible interior a, weight j)
    (hcolumn : ∀ j ∈ interior,
      ((Finset.bipartiteBelow compatible states j).card : ℝ) ≤ K)
    (hboundary : ∀ j ∈ boundary,
      ((Finset.bipartiteBelow compatible states j).card : ℝ) ≤ K) :
    (states.card : ℝ) ≤ (C + (boundary.card : ℝ)) * K := by
  classical
  let good := states.filter (fun a => ∀ j ∈ boundary, ¬ compatible a j)
  let bad := states \ good
  have hgoodsub : good ⊆ states := Finset.filter_subset _ _
  have hgood : (good.card : ℝ) ≤ C * K := by
    apply palette_weighted_list_count good interior weight compatible hP hC hK hw hmass
    · intro a ha
      exact hrow a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
    · intro j hj
      have hsub : Finset.bipartiteBelow compatible good j ⊆
          Finset.bipartiteBelow compatible states j := by
        intro a ha
        obtain ⟨hag, hac⟩ := (Finset.mem_bipartiteBelow compatible).mp ha
        exact (Finset.mem_bipartiteBelow compatible).mpr ⟨hgoodsub hag, hac⟩
      have hle : ((Finset.bipartiteBelow compatible good j).card : ℝ) ≤
          ((Finset.bipartiteBelow compatible states j).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hle.trans (hcolumn j hj)
  have hbadsub : bad ⊆ boundary.biUnion (fun j => Finset.bipartiteBelow compatible states j) := by
    intro a ha
    obtain ⟨has, hag⟩ := Finset.mem_sdiff.mp ha
    have hn : ¬ ∀ j ∈ boundary, ¬ compatible a j := by
      intro hh
      exact hag (Finset.mem_filter.mpr ⟨has, hh⟩)
    push Not at hn
    obtain ⟨j, hj, haj⟩ := hn
    exact Finset.mem_biUnion.mpr
      ⟨j, hj, (Finset.mem_bipartiteBelow compatible).mpr ⟨has, haj⟩⟩
  have hbad : (bad.card : ℝ) ≤ (boundary.card : ℝ) * K := by
    calc
      _ ≤ ((boundary.biUnion (fun j => Finset.bipartiteBelow compatible states j)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hbadsub
      _ ≤ ∑ j ∈ boundary, ((Finset.bipartiteBelow compatible states j).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ boundary, K := Finset.sum_le_sum hboundary
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hpart : bad.card + good.card = states.card := Finset.card_sdiff_add_card_eq_card hgoodsub
  have hpartR : (states.card : ℝ) = (good.card : ℝ) + (bad.card : ℝ) := by
    exact_mod_cast (by omega : states.card = good.card + bad.card)
  rw [hpartR]
  exact (add_le_add hgood hbad).trans_eq (by ring)

end Submission.Obl.k4_scalar_graph_residual_discovery
