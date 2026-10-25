import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PathLemma

/-!
# Paths of length three bound the restricted sumset

The additive half of the graph Balog–Szemerédi–Gowers lemma (paper Lemma 7.1): a path
`a – y – x – b` of length three in `E` gives the triple `(a + y, x + y, x + b)` of sums of edges,
whose alternating sum is `a + b`. For fixed `a, b` the triple determines the path, so many paths
between every pair of `A' × B'` bound `|A' + B'|` by `|C|³`, where `C` is the set of edge sums.
-/

namespace Submission.Obl.k4_graph_bsg

open scoped BigOperators
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The triples of `C³` whose alternating sum is `s`. -/
def sumTriples (C : Finset G) (s : G) : Finset (G × G × G) :=
  (C ×ˢ C ×ˢ C).filter (fun t => t.1 - t.2.1 + t.2.2 = s)

/-- The paths between `a` and `b` inject into the triples of edge sums with alternating sum
`a + b`. -/
theorem card_pathSet_le_card_sumTriples (A B : Finset G) (E : Finset (G × G)) (a b : G) :
    (pathSet A B E a b).card ≤
      (sumTriples (E.image (fun p : G × G => p.1 + p.2)) (a + b)).card := by
  refine Finset.card_le_card_of_injOn (fun q : G × G => (a + q.2, q.1 + q.2, q.1 + b)) ?_ ?_
  · intro q hq
    rw [Finset.mem_coe, pathSet, Finset.mem_filter] at hq
    obtain ⟨_, h1, h2, h3⟩ := hq
    rw [Finset.mem_coe, sumTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    refine ⟨⟨Finset.mem_image.mpr ⟨(a, q.2), h1, rfl⟩, Finset.mem_image.mpr ⟨q, h2, rfl⟩,
      Finset.mem_image.mpr ⟨(q.1, b), h3, rfl⟩⟩, ?_⟩
    show a + q.2 - (q.1 + q.2) + (q.1 + b) = a + b
    abel
  · intro q _ q' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (add_right_cancel h.2.2) (add_left_cancel h.1)

/-- **Triple counting.** If every pair of `A' × B'` is joined by at least `K` paths of length
three in `E`, then `|A' + B'| * K ≤ |C|³`, where `C = {x + y : (x, y) ∈ E}`. -/
theorem triple_count (A B A' B' : Finset G) (E : Finset (G × G)) (K : ℝ)
    (hpath : ∀ a ∈ A', ∀ b ∈ B', K ≤ ((pathSet A B E a b).card : ℝ)) :
    (((A' ×ˢ B').image (fun p : G × G => p.1 + p.2)).card : ℝ) * K ≤
      ((E.image (fun p : G × G => p.1 + p.2)).card : ℝ) ^ 3 := by
  set C := E.image (fun p : G × G => p.1 + p.2) with hC
  set S := (A' ×ˢ B').image (fun p : G × G => p.1 + p.2) with hS
  have hdisj : (S : Set G).PairwiseDisjoint (sumTriples C) := by
    intro s _ s' _ hss'
    rw [Function.onFun, Finset.disjoint_left]
    intro t ht ht'
    rw [sumTriples, Finset.mem_filter] at ht ht'
    exact hss' (ht.2.symm.trans ht'.2)
  have hsub : S.biUnion (sumTriples C) ⊆ C ×ˢ C ×ˢ C := by
    intro t ht
    obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp ht
    exact (Finset.mem_filter.mp hs).1
  have hcard : ∑ s ∈ S, (sumTriples C s).card ≤ C.card ^ 3 := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj, Finset.card_product, Finset.card_product] at h
    calc _ ≤ C.card * (C.card * C.card) := h
      _ = C.card ^ 3 := by ring
  have hlow : ∀ s ∈ S, K ≤ ((sumTriples C s).card : ℝ) := by
    intro s hs
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact (hpath a ha b hb).trans (by exact_mod_cast card_pathSet_le_card_sumTriples A B E a b)
  calc (S.card : ℝ) * K = ∑ s ∈ S, K := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ s ∈ S, ((sumTriples C s).card : ℝ) := Finset.sum_le_sum hlow
    _ ≤ (C.card : ℝ) ^ 3 := by exact_mod_cast hcard

end Submission.Obl.k4_graph_bsg
