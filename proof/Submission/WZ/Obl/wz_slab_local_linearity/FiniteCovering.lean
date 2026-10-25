-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.FiniteCovering.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.Covering

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric

/-- A finite family with at most `N` indices in each doubled-radius neighbourhood
has at most `m*N` indices when its image is covered by `m` balls. -/
lemma card_le_cover_mul {ι X : Type*} [PseudoMetricSpace X]
    (K : Finset ι) (f : ι → X) {r N : ℝ} (hN : 0 ≤ N)
    (hmult : ∀ k ∈ K,
      ((K.filter fun k' => dist (f k) (f k') ≤ 2 * r).card : ℝ) ≤ N)
    {m : ℕ} (c : Fin m → X) (hcover : f '' (K : Set ι) ⊆ ⋃ j, closedBall (c j) r) :
    (K.card : ℝ) ≤ (m : ℝ) * N := by
  classical
  let B : Fin m → Finset ι := fun j => K.filter (fun k => dist (f k) (c j) ≤ r)
  have hB (j : Fin m) : ((B j).card : ℝ) ≤ N := by
    by_cases hj : (B j).Nonempty
    · obtain ⟨k, hk⟩ := hj
      have hk0 := Finset.mem_filter.mp hk
      have hsub : B j ⊆ K.filter (fun k' => dist (f k) (f k') ≤ 2 * r) := by
        intro k' hk'
        obtain ⟨hk'K, hk'd⟩ := Finset.mem_filter.mp hk'
        refine Finset.mem_filter.mpr ⟨hk'K, ?_⟩
        calc
          dist (f k) (f k') ≤ dist (f k) (c j) + dist (f k') (c j) := dist_triangle_right _ _ _
          _ ≤ 2 * r := by linarith [hk0.2]
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hmult k hk0.1)
    · simpa [Finset.not_nonempty_iff_eq_empty.mp hj] using hN
  have hsub : K ⊆ Finset.univ.biUnion B := by
    intro k hk
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ⟨k, hk, rfl⟩)
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hk, hj⟩⟩
  have hcount : K.card ≤ ∑ j : Fin m, (B j).card :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  calc
    (K.card : ℝ) ≤ ∑ j : Fin m, ((B j).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _ : Fin m, N := Finset.sum_le_sum fun j _ => hB j
    _ = (m : ℝ) * N := by simp

/-- A cardinality lower bound and a multiplicity bound imply an entropy lower bound. -/
lemma coverLower_of_card {ι X : Type*} [PseudoMetricSpace X]
    (K : Finset ι) (f : ι → X) {r N H : ℝ} (hN : 0 < N)
    (hmult : ∀ k ∈ K,
      ((K.filter fun k' => dist (f k) (f k') ≤ 2 * r).card : ℝ) ≤ N)
    (hcard : N * H ≤ (K.card : ℝ)) : CoverLower (f '' (K : Set ι)) r H := by
  intro m c hc
  have h := hcard.trans (card_le_cover_mul K f hN.le hmult c hc)
  nlinarith

/-- Pointwise multiplicity bounds multiply for a family of triples in the product metric. -/
lemma triple_multiplicity {ι X : Type*} [PseudoMetricSpace X]
    (K J : Finset ι) (a b : ι → X) (T : Finset (ι × ι × ι)) {r N : ℝ} (hN : 0 ≤ N)
    (hT : T ⊆ K ×ˢ (J ×ˢ J))
    (ha : ∀ k ∈ K, ((K.filter fun k' => dist (a k) (a k') ≤ 2 * r).card : ℝ) ≤ N)
    (hb : ∀ j ∈ J, ((J.filter fun j' => dist (b j) (b j') ≤ 2 * r).card : ℝ) ≤ N) :
    ∀ t ∈ T, ((T.filter fun t' =>
      dist (a t.1, b t.2.1, b t.2.2) (a t'.1, b t'.2.1, b t'.2.2) ≤ 2 * r).card : ℝ) ≤ N ^ 3 := by
  classical
  intro t ht
  have ht' := hT ht
  simp only [Finset.mem_product] at ht'
  have hsub : (T.filter fun t' =>
      dist (a t.1, b t.2.1, b t.2.2) (a t'.1, b t'.2.1, b t'.2.2) ≤ 2 * r) ⊆
      (K.filter fun k' => dist (a t.1) (a k') ≤ 2 * r) ×ˢ
      ((J.filter fun j' => dist (b t.2.1) (b j') ≤ 2 * r) ×ˢ
       (J.filter fun j' => dist (b t.2.2) (b j') ≤ 2 * r)) := by
    intro t' ht'
    obtain ⟨ht'T, hd⟩ := Finset.mem_filter.mp ht'
    have hmem := hT ht'T
    simp only [Finset.mem_product] at hmem
    simp only [Prod.dist_eq, max_le_iff] at hd
    simp only [Finset.mem_product, Finset.mem_filter]
    exact ⟨⟨hmem.1, hd.1⟩, ⟨hmem.2.1, hd.2.1⟩, ⟨hmem.2.2, hd.2.2⟩⟩
  have hcard := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
  simp only [Finset.card_product, Nat.cast_mul] at hcard
  calc
    _ ≤ _ := hcard
    _ ≤ N * (N * N) := mul_le_mul (ha t.1 ht'.1)
      (mul_le_mul (hb t.2.1 ht'.2.1) (hb t.2.2 ht'.2.2) (by positivity) hN)
      (by positivity) hN
    _ = N ^ 3 := by ring

lemma triple_coverLower_of_card {ι X : Type*} [PseudoMetricSpace X]
    (K J : Finset ι) (a b : ι → X) (T : Finset (ι × ι × ι)) {r N H : ℝ} (hN : 0 < N)
    (hT : T ⊆ K ×ˢ (J ×ˢ J))
    (ha : ∀ k ∈ K, ((K.filter fun k' => dist (a k) (a k') ≤ 2 * r).card : ℝ) ≤ N)
    (hb : ∀ j ∈ J, ((J.filter fun j' => dist (b j) (b j') ≤ 2 * r).card : ℝ) ≤ N)
    (hcard : N ^ 3 * H ≤ (T.card : ℝ)) :
    CoverLower ((fun t : ι × ι × ι => (a t.1, b t.2.1, b t.2.2)) '' (T : Set _)) r H :=
  coverLower_of_card T _ (by positivity) (triple_multiplicity K J a b T hN.le hT ha hb) hcard

end WangZahlLot.Obl.wz_slab_local_linearity
