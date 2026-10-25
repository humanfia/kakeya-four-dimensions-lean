import Submission.Lib.K4ModelReduction.CellAveraging

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-! The integrated mesh-averaging estimate for joint base flattening. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory
open scoped ENNReal

/-- Uniform redistribution of one coordinate inside its mesh cells changes
a bounded polynomial sign-table density by at most `4 M D ρ` times the
volume of the other parameters. This estimate is uniform in all coefficients. -/
theorem polynomial_cell_averaging_product
    {Y ι : Type*} [MeasurableSpace Y] [Fintype ι] (μ : Measure Y)
    (p : Y → ι → Polynomial ℝ) (f : Y → ℝ → ℝ) (M : ℝ) (D : ℕ)
    (hf : Measurable (Function.uncurry f))
    (hM : 0 ≤ M) (hbound : ∀ y x, |f y x| ≤ M)
    (hdepend : ∀ y x x', (∀ i, (p y i).eval x ≤ 0 ↔ (p y i).eval x' ≤ 0) →
      f y x = f y x')
    (hdegree : ∀ y, ∑ i, (p y i).natDegree ≤ D)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ z : Y × ℝ, ENNReal.ofReal |meshAverage (f z.1) ρ z.2 - f z.1 z.2| ∂μ.prod volume) ≤
      ENNReal.ofReal (4 * M * (D : ℝ) * ρ) * μ Set.univ := by
  have hG : Measurable (fun z : Y × ℝ =>
      ENNReal.ofReal |meshAverage (f z.1) ρ z.2 - f z.1 z.2|) :=
    ENNReal.measurable_ofReal.comp (((meshAverage_measurable f hf hρ).sub hf).abs)
  calc
    _ = ∫⁻ y, ∫⁻ x : ℝ, ENNReal.ofReal |meshAverage (f y) ρ x - f y x| ∂volume ∂μ :=
      lintegral_prod _ hG.aemeasurable
    _ ≤ ∫⁻ _y, ENNReal.ofReal (4 * M * (D : ℝ) * ρ) ∂μ := by
      apply lintegral_mono
      intro y
      have hreal : ((∑ i, (p y i).natDegree : ℕ) : ℝ) ≤ (D : ℝ) := by
        exact_mod_cast hdegree y
      refine (polynomial_cell_averaging_error_bound (p y) (f y) M hM
        (hbound y) (hdepend y) hρ).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hreal (by positivity)) hρ.le
    _ = _ := lintegral_const _

end Submission.Lib.K4ModelReduction
