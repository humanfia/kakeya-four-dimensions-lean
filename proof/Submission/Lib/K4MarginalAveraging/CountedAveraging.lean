/- Adapted from: here:o009
Original explicit countable-label marginal and averaging proofs developed in this workspace. -/

import Submission.Lib.K4MarginalAveraging.CountedMarginal
import Submission.Lib.K4ModelReduction.CellMass

/-! Averaging preserves the joint countable labels when they depend on
hidden parameters alone, as in the native sheared observation chart. -/

namespace Submission.Lib.K4MarginalAveraging

open MeasureTheory
open scoped ENNReal
open Submission.Lib.K4ModelReduction

theorem meshAverage_realCountedMarginal {Y A : Type*}
    [MeasurableSpace Y] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (f : Y → ℝ → ℝ) (hf : Measurable (Function.uncurry f))
    (L : Y → A) (hL : Measurable L)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ y t, |f y t| ≤ M)
    {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) (a : A) :
    meshAverage (fun t => realCountedMarginal μ f (fun z => L z.1) (t, a)) ρ x =
      realCountedMarginal μ (fun y t => meshAverage (f y) ρ t) (fun z => L z.1) (x, a) := by
  classical
  let F : Y → ℝ → ℝ := fun y t => if L y = a then f y t else 0
  have hF : Measurable (Function.uncurry F) :=
    hf.indicator (measurableSet_eq_fun (hL.comp measurable_fst) measurable_const)
  have hFb : ∀ y t, |F y t| ≤ M := by
    intro y t
    by_cases hy : L y = a
    · simpa only [F, hy, ↓reduceIte] using hbound y t
    · simpa only [F, hy, ↓reduceIte, abs_zero] using hM
  calc
    _ = meshAverage (fun t => ∫ y, F y t ∂μ) ρ x := rfl
    _ = ∫ y, meshAverage (F y) ρ x ∂μ := meshAverage_integral μ F hF M hFb hρ x
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      by_cases hy : L y = a <;> simp only [F, hy, ↓reduceIte,
        meshAverage, integral_zero]

/-- Base-cell constancy before hidden integration gives a common table
for every retained discrete observation label. -/
theorem realCountedMarginal_same_cell {Y A ι : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f : Y → (ι → ℝ) → ℝ) (L : Y → A) (ρ : ℝ)
    (hconstant : ∀ y x x', (∀ i, ⌊x i / ρ⌋ = ⌊x' i / ρ⌋) → f y x = f y x')
    (x x' : ι → ℝ) (hfloor : ∀ i, ⌊x i / ρ⌋ = ⌊x' i / ρ⌋) (a : A) :
    realCountedMarginal μ f (fun z => L z.1) (x, a) =
      realCountedMarginal μ f (fun z => L z.1) (x', a) := by
  classical
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  by_cases hy : L y = a <;>
    simp only [hy, ↓reduceIte, hconstant y x x' hfloor]

end Submission.Lib.K4MarginalAveraging
