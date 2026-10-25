-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap.Removal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Heavy-strip removal

The elementary half of the OSW bootstrapping step.  Starting from a dense
relation `T ⊆ G ×ˢ G'`, delete every pair `(b, b')` such that `b'` lies in a
*heavy* strip through `b` at some dyadic scale `2 ^ j * δ`.  What is left is
thin at every scale by construction; it stays dense as soon as the heavy pairs
of each dyadic scale are few (`thin_of_heavy_bounds`).
-/

namespace WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap

/-- The plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The `T`-neighbours of `b` in the open strip of half-width `w` normal to `e`
(exactly the set counted in the frozen thin-tubes condition). -/
def strip (T : Set (E2 × E2)) (b e : E2) (w : ℝ) : Set E2 :=
  {b' | (b, b') ∈ T ∧ |inner ℝ (b' - b) e| < w}

/-- The pairs of `T` lying in a strip of half-width `w` through their first
point whose `T`-count exceeds `lam`. -/
def heavyPairs (T : Set (E2 × E2)) (w lam : ℝ) : Set (E2 × E2) :=
  {p | p ∈ T ∧ ∃ e : E2, ‖e‖ = 1 ∧ |inner ℝ (p.2 - p.1) e| < w ∧
    lam < ((strip T p.1 e w).ncard : ℝ)}

lemma heavyPairs_subset (T : Set (E2 × E2)) (w lam : ℝ) : heavyPairs T w lam ⊆ T :=
  fun _ hp => hp.1

lemma strip_mono {T T' : Set (E2 × E2)} (hT : T' ⊆ T) {b e : E2} {w w' : ℝ} (hw : w' ≤ w) :
    strip T' b e w' ⊆ strip T b e w :=
  fun _ hb' => ⟨hT hb'.1, lt_of_lt_of_le hb'.2 hw⟩

lemma strip_subset_snd (T : Set (E2 × E2)) {G G' : Set E2} (hT : T ⊆ G ×ˢ G') (b e : E2)
    (w : ℝ) : strip T b e w ⊆ G' :=
  fun _ hb' => (hT hb'.1).2

/-- The `j`-th dyadic scale. -/
noncomputable def dyad (δ : ℝ) (j : ℕ) : ℝ := 2 ^ j * δ

/-- The pairs removed at the dyadic scales below `N`. -/
def removed (T : Set (E2 × E2)) (δ : ℝ) (lam : ℕ → ℝ) (N : ℕ) : Set (E2 × E2) :=
  ⋃ j ∈ Finset.range N, heavyPairs T (2 * dyad δ j) (lam j)

lemma ncard_biUnion_range_le {α : Type*} (H : ℕ → Set α) (N : ℕ) :
    ((⋃ j ∈ Finset.range N, H j).ncard : ℝ) ≤ ∑ j ∈ Finset.range N, ((H j).ncard : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, Finset.sum_insert Finset.notMem_range_self]
    have h1 := Set.ncard_union_le (H n) (⋃ j ∈ Finset.range n, H j)
    have h1' : (((H n) ∪ ⋃ j ∈ Finset.range n, H j).ncard : ℝ) ≤
        ((H n).ncard : ℝ) + ((⋃ j ∈ Finset.range n, H j).ncard : ℝ) := by
      exact_mod_cast h1
    linarith

/-- Heavy-strip removal.  If at every dyadic scale `j < N` the heavy pairs
(threshold `K' * (2 ^ j * δ) ^ σ' * #G'`, half-width `2 * 2 ^ j * δ`) number at
most `η j * #G * #G'`, there are none at the scales `j ≥ N`, and
`∑ η ≤ 3 c`, then `T` minus the heavy pairs is `(σ', K')`-thin and still has
density `1 - 4 c`. -/
theorem thin_of_heavy_bounds {δ σ' K' c : ℝ} (hδ : 0 < δ) (hσ' : 0 ≤ σ') (hK' : 0 ≤ K')
    {G G' : Set E2} (hG : G.Finite) (hG' : G'.Finite)
    {T : Set (E2 × E2)} (hT : T ⊆ G ×ˢ G')
    (hdense : (1 - c) * G.ncard * G'.ncard ≤ (T.ncard : ℝ))
    (η : ℕ → ℝ) (N : ℕ)
    (hbound : ∀ j < N, ((heavyPairs T (2 * dyad δ j) (K' * dyad δ j ^ σ' * G'.ncard)).ncard : ℝ)
      ≤ η j * G.ncard * G'.ncard)
    (hzero : ∀ j, N ≤ j → heavyPairs T (2 * dyad δ j) (K' * dyad δ j ^ σ' * G'.ncard) = ∅)
    (hsum : ∑ j ∈ Finset.range N, η j ≤ 3 * c) :
    ∃ T' : Set (E2 × E2), T' ⊆ G ×ˢ G' ∧ (1 - 4 * c) * G.ncard * G'.ncard ≤ (T'.ncard : ℝ) ∧
      ∀ b ∈ G, ∀ e : E2, ‖e‖ = 1 → ∀ r : ℝ, δ ≤ r →
        ({b' | (b, b') ∈ T' ∧ |inner ℝ (b' - b) e| < r}.ncard : ℝ) ≤ K' * r ^ σ' * G'.ncard := by
  set lam : ℕ → ℝ := fun j => K' * dyad δ j ^ σ' * G'.ncard with hlam
  set U := removed T δ lam N with hU
  have hTfin : T.Finite := (hG.prod hG').subset hT
  refine ⟨T \ U, Set.sdiff_subset.trans hT, ?_, ?_⟩
  · -- density
    have hUfin : U.Finite := by
      apply Set.Finite.biUnion (Finset.finite_toSet _)
      intro j _
      exact hTfin.subset (heavyPairs_subset _ _ _)
    have h1 : (T.ncard : ℝ) ≤ ((T \ U).ncard : ℝ) + (U.ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard_sdiff_add_ncard T U hUfin
    have h2 : (U.ncard : ℝ) ≤ ∑ j ∈ Finset.range N,
        ((heavyPairs T (2 * dyad δ j) (lam j)).ncard : ℝ) :=
      ncard_biUnion_range_le _ N
    have h3 : ∑ j ∈ Finset.range N, ((heavyPairs T (2 * dyad δ j) (lam j)).ncard : ℝ) ≤
        ∑ j ∈ Finset.range N, η j * G.ncard * G'.ncard := by
      apply Finset.sum_le_sum
      intro j hj
      exact hbound j (Finset.mem_range.mp hj)
    have h4 : ∑ j ∈ Finset.range N, η j * G.ncard * G'.ncard =
        (∑ j ∈ Finset.range N, η j) * G.ncard * G'.ncard := by
      rw [Finset.sum_mul, Finset.sum_mul]
    have hGG : (0 : ℝ) ≤ G.ncard * G'.ncard := by positivity
    have h5 : (∑ j ∈ Finset.range N, η j) * G.ncard * G'.ncard ≤ 3 * c * G.ncard * G'.ncard := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right hsum hGG
    nlinarith
  · -- thinness
    intro b hb e he r hr
    have hr1 : 1 ≤ r / δ := by rw [le_div_iff₀ hδ]; linarith
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hr1 (by norm_num : (1 : ℝ) < 2)
    have hdj : dyad δ j ≤ r := by
      unfold dyad; rwa [le_div_iff₀ hδ] at hj1
    have hdj2 : r < 2 * dyad δ j := by
      unfold dyad; rw [div_lt_iff₀ hδ, pow_succ] at hj2; linarith
    have hdpos : 0 < dyad δ j := by unfold dyad; positivity
    have hsub : {b' | (b, b') ∈ T \ U ∧ |inner ℝ (b' - b) e| < r} ⊆ strip T b e (2 * dyad δ j) :=
      fun b' hb' => ⟨hb'.1.1, lt_of_lt_of_le hb'.2 hdj2.le⟩
    have hstripfin : (strip T b e (2 * dyad δ j)).Finite :=
      hG'.subset (strip_subset_snd T hT b e _)
    have hr0 : 0 ≤ r := hδ.le.trans hr
    have hRHS : 0 ≤ K' * r ^ σ' * G'.ncard := by positivity
    by_cases hheavy : lam j < ((strip T b e (2 * dyad δ j)).ncard : ℝ)
    · -- every such pair was removed
      have hempty : {b' | (b, b') ∈ T \ U ∧ |inner ℝ (b' - b) e| < r} = ∅ := by
        ext b'
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hbT hin
        apply hbT.2
        have hp : (b, b') ∈ heavyPairs T (2 * dyad δ j) (lam j) :=
          ⟨hbT.1, e, he, lt_of_lt_of_le hin hdj2.le, hheavy⟩
        by_cases hjN : j < N
        · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hjN)) hp
        · have := hzero j (not_lt.mp hjN)
          rw [this] at hp
          exact absurd hp (Set.notMem_empty _)
      rw [hempty, Set.ncard_empty]
      simpa using hRHS
    · replace hheavy := not_lt.mp hheavy
      have h1 : (({b' | (b, b') ∈ T \ U ∧ |inner ℝ (b' - b) e| < r}.ncard : ℕ) : ℝ) ≤
          ((strip T b e (2 * dyad δ j)).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hstripfin
      have h2 : lam j ≤ K' * r ^ σ' * G'.ncard := by
        simp only [hlam]
        have : dyad δ j ^ σ' ≤ r ^ σ' := Real.rpow_le_rpow hdpos.le hdj hσ'
        have hG'0 : (0 : ℝ) ≤ G'.ncard := by positivity
        have := mul_le_mul_of_nonneg_left this hK'
        exact mul_le_mul_of_nonneg_right this hG'0
      linarith

end WangZahlLot.Obl.wz_osw_thin_tubes_bootstrap
