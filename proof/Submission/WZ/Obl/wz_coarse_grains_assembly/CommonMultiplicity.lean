-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.CommonMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

/-- A size coloring and weighted pigeonholing select one common size
interval, with its lower endpoint attained by a retained index. -/
theorem select_common_size {ι : Type*} [DecidableEq ι] {n K : ℕ} {R : ℝ}
    (hK : 0 < K) (color : ℕ → Fin K)
    (hcolor : ∀ a b : ℕ, 0 < a → a ≤ n → 0 < b → b ≤ n →
      color a = color b → (a : ℝ) ≤ R * b)
    (B : Finset ι) (size : ι → ℕ) (weight : ι → ENNReal)
    (hsize : ∀ k ∈ B, 0 < size k ∧ size k ≤ n)
    (hpos : 0 < ∑ k ∈ B, weight k) :
    ∃ (A : Finset ι) (M : ℕ), A ⊆ B ∧ A.Nonempty ∧ 0 < M ∧
      (∑ k ∈ B, weight k) ≤ (K : ENNReal) * ∑ k ∈ A, weight k ∧
      ∀ k ∈ A, M ≤ size k ∧ (size k : ℝ) ≤ R * M := by
  classical
  obtain ⟨a, ha⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color
    hK B (fun k => color (size k)) weight
  let A := B.filter (fun k => color (size k) = a)
  have hAB : A ⊆ B := Finset.filter_subset _ _
  have hA : A.Nonempty := by
    by_contra hempty
    have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    change (∑ k ∈ B, weight k) ≤ (K : ENNReal) * ∑ k ∈ A, weight k at ha
    rw [he, Finset.sum_empty, mul_zero] at ha
    exact (not_le_of_gt hpos) ha
  obtain ⟨k₀, hk₀, hmin⟩ := Finset.exists_min_image A size hA
  refine ⟨A, size k₀, hAB, hA, (hsize k₀ (hAB hk₀)).1, ha, ?_⟩
  intro k hk
  refine ⟨hmin k hk, ?_⟩
  obtain ⟨hkp, hkn⟩ := hsize k (hAB hk)
  obtain ⟨h₀p, h₀n⟩ := hsize k₀ (hAB hk₀)
  apply hcolor _ _ hkp hkn h₀p h₀n
  exact (Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hk₀).2.symm

/-- A common interval for the ceilings of the real multiplicity levels
gives an interval with integer lower endpoint for every point count. -/
theorem multiplicity_window_of_ceiling {n M : ℕ} {m R : ℝ}
    (Z : Fin n → Set V) (hlo : M ≤ ⌈m⌉₊) (hhi : (⌈m⌉₊ : ℝ) ≤ R * M)
    (hmult : ∀ p, (∃ i, p ∈ Z i) → q n {i | p ∈ Z i} ∈ Set.Icc m (2 * m)) :
    ∀ p, (∃ i, p ∈ Z i) →
      (M : ℝ) ≤ q n {i | p ∈ Z i} ∧ q n {i | p ∈ Z i} ≤ (2 * R) * M := by
  intro p hp
  obtain ⟨hl, hu⟩ := hmult p hp
  have hceil : ⌈m⌉₊ ≤ ({i | p ∈ Z i} : Set (Fin n)).ncard := Nat.ceil_le.mpr hl
  constructor
  · exact_mod_cast hlo.trans hceil
  · have hc := Nat.le_ceil m
    nlinarith

/-- Positive-mass multiplicity levels have ceilings in the finite range
needed by the size-coloring API. -/
theorem multiplicity_ceiling_bounds {n : ℕ} {m : ℝ} {Z : Fin n → Set V}
    (hne : ∃ p i, p ∈ Z i)
    (hmult : ∀ p, (∃ i, p ∈ Z i) → q n {i | p ∈ Z i} ∈ Set.Icc m (2 * m)) :
    0 < ⌈m⌉₊ ∧ ⌈m⌉₊ ≤ n := by
  obtain ⟨p, i, hi⟩ := hne
  have hcountpos : 0 < q n {i | p ∈ Z i} := by
    apply Nat.cast_pos.mpr
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨i, hi⟩
  obtain ⟨hl, hu⟩ := hmult p ⟨i, hi⟩
  have hm : 0 < m := by linarith
  refine ⟨Nat.ceil_pos.mpr hm, ?_⟩
  have hn : q n {i | p ∈ Z i} ≤ n := by
    apply Nat.cast_le.mpr
    exact (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)).trans_eq (by simp)
  exact Nat.ceil_le.mpr (hl.trans hn)

end WangZahlLot.Obl.wz_coarse_grains_assembly
