import Mathlib

/-!
# Dyadic coarsening of an integer coordinate

The hidden bins of an observation at depth `b ≤ L` are unions of exactly `2 ^ m`
hidden bins at depth `L`.  Pushing a measure with density forward along
`n ↦ n / 2 ^ m` in its integer coordinate therefore sums the density over the
`2 ^ m` fine indices of each coarse index.  We record this for the reference
measures `(α × count) × β` (joint observations) and `α × count` (pure
observations).
-/

noncomputable section

namespace Submission.Lib.K4ExactProblemOps

open MeasureTheory

/-- The coarse integer index `n / 2 ^ m`. -/
def coarseIdx (m : ℕ) (n : ℤ) : ℤ := n / ((2 ^ m : ℕ) : ℤ)

/-- The `i`-th fine index inside the coarse index `n'`. -/
def fineIdx (m : ℕ) (n' : ℤ) (i : Fin (2 ^ m)) : ℤ := n' * ((2 ^ m : ℕ) : ℤ) + (i : ℕ)

theorem fineIdx_eq_symm (m : ℕ) (n' : ℤ) (i : Fin (2 ^ m)) :
    fineIdx m n' i = (Int.divModEquiv (2 ^ m)).symm (n', i) := rfl

theorem coarseIdx_fineIdx (m : ℕ) (n' : ℤ) (i : Fin (2 ^ m)) :
    coarseIdx m (fineIdx m n' i) = n' := by
  have h := congrArg Prod.fst ((Int.divModEquiv (2 ^ m)).apply_symm_apply (n', i))
  rw [← fineIdx_eq_symm, Int.divModEquiv_apply] at h
  exact h

/-- Reindex a sum over `ℤ` by coarse indices and their fine indices. -/
theorem tsum_int_eq_tsum_fine (m : ℕ) (h : ℤ → ENNReal) :
    ∑' n, h n = ∑' n', ∑ i : Fin (2 ^ m), h (fineIdx m n' i) := by
  rw [← (Int.divModEquiv (2 ^ m)).symm.tsum_eq h]
  have : ∀ p : ℤ × Fin (2 ^ m), h ((Int.divModEquiv (2 ^ m)).symm p) =
      (fun a b => h (fineIdx m a b)) p.1 p.2 := fun p => rfl
  simp_rw [this]
  rw [ENNReal.tsum_prod (f := fun a b => h (fineIdx m a b))]
  congr 1
  ext n'
  rw [tsum_fintype]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-! ## Joint observations `(X × ℤ) × Y` -/

/-- Coarsening of the integer coordinate of `(X × ℤ) × Y`. -/
def coarsenJ (m : ℕ) (z : (X × ℤ) × Y) : (X × ℤ) × Y := ((z.1.1, coarseIdx m z.1.2), z.2)

/-- The fiber sum of a density over the fine indices of a coarse index. -/
def fiberSumJ (m : ℕ) (G : (X × ℤ) × Y → ENNReal) (z : (X × ℤ) × Y) : ENNReal :=
  ∑ i : Fin (2 ^ m), G ((z.1.1, fineIdx m z.1.2 i), z.2)

theorem measurable_coarsenJ (m : ℕ) : Measurable (coarsenJ (X := X) (Y := Y) m) := by
  unfold coarsenJ
  refine Measurable.prodMk (Measurable.prodMk measurable_fst.fst ?_) measurable_snd
  exact (measurable_of_countable (coarseIdx m)).comp measurable_fst.snd

theorem measurable_fiberSumJ (m : ℕ) {G : (X × ℤ) × Y → ENNReal} (hG : Measurable G) :
    Measurable (fiberSumJ m G) := by
  unfold fiberSumJ
  refine Finset.measurable_fun_sum _ fun i _ => hG.comp ?_
  refine Measurable.prodMk (Measurable.prodMk measurable_fst.fst ?_) measurable_snd
  exact (measurable_of_countable (fun n => fineIdx m n i)).comp measurable_fst.snd

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem fiberSumJ_add (m : ℕ) (G G' : (X × ℤ) × Y → ENNReal) :
    fiberSumJ m (G + G') = fiberSumJ m G + fiberSumJ m G' := by
  ext z
  simp [fiberSumJ, Finset.sum_add_distrib]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem fiberSumJ_mono (m : ℕ) {G G' : (X × ℤ) × Y → ENNReal} (h : G ≤ G') :
    fiberSumJ m G ≤ fiberSumJ m G' := fun _ =>
  Finset.sum_le_sum fun _ _ => h _

/-- Pushing a density forward along the coarsening sums it over each fiber. -/
theorem map_coarsenJ_withDensity (m : ℕ) (α : Measure X) (β : Measure Y) [SFinite β]
    {G : (X × ℤ) × Y → ENNReal} (hG : Measurable G) :
    Measure.map (coarsenJ m) (((α.prod Measure.count).prod β).withDensity G) =
      ((α.prod Measure.count).prod β).withDensity (fiberSumJ m G) := by
  ext S hS
  have hS' : MeasurableSet (coarsenJ (X := X) (Y := Y) m ⁻¹' S) := measurable_coarsenJ m hS
  rw [Measure.map_apply (measurable_coarsenJ m) hS, withDensity_apply _ hS',
    withDensity_apply _ hS, ← lintegral_indicator hS', ← lintegral_indicator hS]
  have hF₁ : Measurable ((coarsenJ (X := X) (Y := Y) m ⁻¹' S).indicator G) :=
    hG.indicator hS'
  have hF₂ : Measurable (S.indicator (fiberSumJ m G)) :=
    (measurable_fiberSumJ m hG).indicator hS
  rw [lintegral_prod _ hF₁.aemeasurable, lintegral_prod _ hF₂.aemeasurable,
    lintegral_prod _ (hF₁.lintegral_prod_right' (ν := β)).aemeasurable,
    lintegral_prod _ (hF₂.lintegral_prod_right' (ν := β)).aemeasurable]
  congr 1
  ext x
  rw [lintegral_count, lintegral_count, tsum_int_eq_tsum_fine m]
  congr 1
  ext n'
  have hmeas : ∀ i : Fin (2 ^ m), Measurable fun y : Y =>
      (coarsenJ (X := X) (Y := Y) m ⁻¹' S).indicator G ((x, fineIdx m n' i), y) := by
    intro i
    exact hF₁.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_finsetSum _ fun i _ => hmeas i]
  congr 1
  ext y
  by_cases hy : ((x, n'), y) ∈ S
  · have hy' : ∀ i : Fin (2 ^ m), ((x, fineIdx m n' i), y) ∈ coarsenJ m ⁻¹' S := by
      intro i
      simpa [coarsenJ, coarseIdx_fineIdx] using hy
    simp only [Set.indicator_of_mem (hy' _), Set.indicator_of_mem hy, fiberSumJ]
  · have hy' : ∀ i : Fin (2 ^ m), ((x, fineIdx m n' i), y) ∉ coarsenJ m ⁻¹' S := by
      intro i
      simpa [coarsenJ, coarseIdx_fineIdx] using hy
    simp only [Set.indicator_of_notMem (hy' _), Set.indicator_of_notMem hy,
      Finset.sum_const_zero]

/-! ## Pure observations `X × ℤ` -/

/-- Coarsening of the integer coordinate of `X × ℤ`. -/
def coarsenO (m : ℕ) (z : X × ℤ) : X × ℤ := (z.1, coarseIdx m z.2)

/-- The fiber sum of a pure density. -/
def fiberSumO (m : ℕ) (g : X × ℤ → ENNReal) (z : X × ℤ) : ENNReal :=
  ∑ i : Fin (2 ^ m), g (z.1, fineIdx m z.2 i)

theorem measurable_coarsenO (m : ℕ) : Measurable (coarsenO (X := X) m) := by
  unfold coarsenO
  exact Measurable.prodMk measurable_fst
    ((measurable_of_countable (coarseIdx m)).comp measurable_snd)

theorem measurable_fiberSumO (m : ℕ) {g : X × ℤ → ENNReal} (hg : Measurable g) :
    Measurable (fiberSumO m g) := by
  unfold fiberSumO
  refine Finset.measurable_fun_sum _ fun i _ => hg.comp ?_
  exact Measurable.prodMk measurable_fst
    ((measurable_of_countable (fun n => fineIdx m n i)).comp measurable_snd)

theorem map_coarsenO_withDensity (m : ℕ) (α : Measure X)
    {g : X × ℤ → ENNReal} (hg : Measurable g) :
    Measure.map (coarsenO m) ((α.prod Measure.count).withDensity g) =
      (α.prod Measure.count).withDensity (fiberSumO m g) := by
  ext S hS
  have hS' : MeasurableSet (coarsenO (X := X) m ⁻¹' S) := measurable_coarsenO m hS
  rw [Measure.map_apply (measurable_coarsenO m) hS, withDensity_apply _ hS',
    withDensity_apply _ hS, ← lintegral_indicator hS', ← lintegral_indicator hS]
  have hF₁ : Measurable ((coarsenO (X := X) m ⁻¹' S).indicator g) := hg.indicator hS'
  have hF₂ : Measurable (S.indicator (fiberSumO m g)) :=
    (measurable_fiberSumO m hg).indicator hS
  rw [lintegral_prod _ hF₁.aemeasurable, lintegral_prod _ hF₂.aemeasurable]
  congr 1
  ext x
  rw [lintegral_count, lintegral_count, tsum_int_eq_tsum_fine m]
  congr 1
  ext n'
  by_cases hy : (x, n') ∈ S
  · have hy' : ∀ i : Fin (2 ^ m), (x, fineIdx m n' i) ∈ coarsenO m ⁻¹' S := by
      intro i
      simpa [coarsenO, coarseIdx_fineIdx] using hy
    simp only [Set.indicator_of_mem (hy' _), Set.indicator_of_mem hy, fiberSumO]
  · have hy' : ∀ i : Fin (2 ^ m), (x, fineIdx m n' i) ∉ coarsenO m ⁻¹' S := by
      intro i
      simpa [coarsenO, coarseIdx_fineIdx] using hy
    simp only [Set.indicator_of_notMem (hy' _), Set.indicator_of_notMem hy,
      Finset.sum_const_zero]

end Submission.Lib.K4ExactProblemOps
