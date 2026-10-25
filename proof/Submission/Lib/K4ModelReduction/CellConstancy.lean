import Submission.Lib.K4ModelReduction.CoordinateAveraging

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Coordinate redistribution produces densities constant on rectangular mesh cells. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory
open scoped ENNReal

def constantOnCoordinateCells {ι : Type*} (f : (ι → ℝ) → ℝ) (ρ : ℝ) (i : ι) : Prop :=
  ∀ x y, (∀ j, j ≠ i → x j = y j) → ⌊x i / ρ⌋ = ⌊y i / ρ⌋ → f x = f y

theorem coordinateAverage_constant {n : ℕ} (i : Fin (n + 1)) (M : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M) :
    constantOnCoordinateCells (coordinateAverage i M hρ f).val ρ i := by
  intro x y hother hfloor
  rw [coordinateAverage_eq, coordinateAverage_eq]
  have hfun : (fun t => f.val (Function.update x i t)) =
      (fun t => f.val (Function.update y i t)) := by
    funext t
    apply congrArg f.val
    funext j
    by_cases hji : j = i
    · subst j; simp
    · simpa only [Function.update_of_ne hji] using hother j hji
  rw [hfun]
  simp only [meshAverage, meshCell, hfloor]

theorem coordinateAverage_preserves_constant {n : ℕ} (i j : Fin (n + 1)) (M : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : constantOnCoordinateCells f.val ρ i) :
    constantOnCoordinateCells (coordinateAverage j M hρ f).val ρ i := by
  by_cases hji : j = i
  · subst j; exact coordinateAverage_constant i M hρ f
  intro x y hother hfloor
  rw [coordinateAverage_eq, coordinateAverage_eq, hother j hji]
  apply congrArg (fun g : ℝ → ℝ => meshAverage g ρ (y j))
  funext t
  apply hf
  · intro k hki
    by_cases hkj : k = j
    · subst k; simp
    · simpa only [Function.update_of_ne hkj] using hother k hki
  · simpa only [Function.update_of_ne (Ne.symm hji)] using hfloor

theorem coordinate_averaging_constant {n : ℕ} (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (L : List (Fin (n + 1))) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M) :
    ∀ i ∈ L, constantOnCoordinateCells
      (L.foldr (fun j g => coordinateAverage j M hρ g) f).val ρ i := by
  induction L with
  | nil => simp
  | cons j L ih =>
    intro i hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact coordinateAverage_constant i M hρ _
    · exact coordinateAverage_preserves_constant i j M hρ _ (ih i hi)

theorem eq_of_constantOnCoordinateCells {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (ρ : ℝ) (hf : ∀ i, constantOnCoordinateCells f ρ i)
    (x y : ι → ℝ) (hfloor : ∀ i, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) : f x = f y := by
  have hfinite (S : Finset ι) : ∀ x y : ι → ℝ,
      (∀ j ∉ S, x j = y j) → (∀ j ∈ S, ⌊x j / ρ⌋ = ⌊y j / ρ⌋) → f x = f y := by
    induction S using Finset.induction_on with
    | empty =>
      intro x y heq _
      congr 1
      exact funext fun j => heq j (by simp)
    | @insert i S hi ih =>
      intro x y hother hbin
      let z := Function.update x i (y i)
      have hxz : f x = f z := by
        apply hf i
        · intro j hji
          simp only [z, Function.update_of_ne hji]
        · simpa [z] using hbin i (Finset.mem_insert_self i S)
      refine hxz.trans (ih z y ?_ ?_)
      · intro j hj
        by_cases hji : j = i
        · subst j; simp [z]
        · simpa only [z, Function.update_of_ne hji] using
            hother j (by simp only [Finset.mem_insert, not_or]; exact ⟨hji, hj⟩)
      · intro j hj
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        simpa only [z, Function.update_of_ne hji] using hbin j (Finset.mem_insert_of_mem hj)
  exact hfinite Finset.univ x y (by simp) (fun i _ => hfloor i)

/-- Averaging every base coordinate yields an actual table on rectangular
mesh cells, with no remaining dependence on positions inside a cell. -/
theorem coordinate_averaging_same_cell {n : ℕ} (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (L : List (Fin (n + 1))) (hL : ∀ i, i ∈ L)
    (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (x y : Fin (n + 1) → ℝ) (hfloor : ∀ i, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) :
    (L.foldr (fun i g => coordinateAverage i M hρ g) f).val x =
      (L.foldr (fun i g => coordinateAverage i M hρ g) f).val y :=
  eq_of_constantOnCoordinateCells _ ρ
    (fun i => coordinate_averaging_constant M hρ L f i (hL i)) x y hfloor

theorem coordinate_averaging_nonneg {n : ℕ} (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (L : List (Fin (n + 1))) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : ∀ x, 0 ≤ f.val x) :
    ∀ x, 0 ≤ (L.foldr (fun i g => coordinateAverage i M hρ g) f).val x := by
  induction L with
  | nil => exact hf
  | cons i L ih =>
    exact averageInSplit_nonneg (coordinateSplit i) M hρ _ ih

theorem coordinate_averaging_mass {n : ℕ} (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (L : List (Fin (n + 1))) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : ∀ x, 0 ≤ f.val x) :
    (∫⁻ x, ENNReal.ofReal ((L.foldr (fun i g => coordinateAverage i M hρ g) f).val x)) =
      ∫⁻ x, ENNReal.ofReal (f.val x) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    calc
      _ = ∫⁻ x, ENNReal.ofReal ((L.foldr (fun i g => coordinateAverage i M hρ g) f).val x) :=
        coordinateAverage_mass i M hρ _ (coordinate_averaging_nonneg M hρ L f hf)
      _ = _ := ih

theorem coordinate_averaging_error_le {n : ℕ} (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (L : List (Fin (n + 1))) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (E : ℝ≥0∞)
    (hE : ∀ i ∈ L, densityL1Distance volume (coordinateAverage i M hρ f).val f.val ≤ E) :
    densityL1Distance volume (L.foldr (fun i g => coordinateAverage i M hρ g) f).val f.val ≤
      (L.length : ℝ≥0∞) * E := by
  refine (coordinate_averaging_error M hρ L f).trans ?_
  have h := List.sum_le_length_nsmul
    (L.map (fun i => densityL1Distance volume (coordinateAverage i M hρ f).val f.val)) E ?_
  · simpa only [List.length_map, nsmul_eq_mul] using h
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact hE i hi

end Submission.Lib.K4ModelReduction
