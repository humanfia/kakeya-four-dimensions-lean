import Mathlib

namespace Submission.Obl.k4_quadratic_slope_volume

open Set MeasureTheory
open scoped ENNReal

/-- Change of variables on an injective piece converts a uniform lower bound on
the Jacobian into an upper bound on the measure of that piece. -/
theorem jacobian_mul_measure_le_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Set E) (hS : MeasurableSet S) (f : E → E) (f' : E → E →L[ℝ] E)
    (hf' : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x) (hf : InjOn f S)
    (J : ℝ) (hJ : ∀ x ∈ S, J ≤ |(f' x).det|) :
    ENNReal.ofReal J * μ S ≤ μ (f '' S) := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image μ hS hf' hf]
  calc
    ENNReal.ofReal J * μ S = ∫⁻ _ in S, ENNReal.ofReal J ∂μ :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in S, ENNReal.ofReal |(f' x).det| ∂μ := by
      apply setLIntegral_mono' hS
      intro x hx
      exact ENNReal.ofReal_le_ofReal (hJ x hx)

/-- Finitely many injective pieces suffice for the multiplicity version of the
sweep estimate; the pieces may overlap. -/
theorem jacobian_mul_measure_le_finite_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {N : ℕ} (S : Set E) (pieces : Fin N → Set E)
    (hcover : S ⊆ ⋃ i, pieces i) (hpieces : ∀ i, MeasurableSet (pieces i))
    (f : E → E) (f' : E → E →L[ℝ] E)
    (hf' : ∀ i x, x ∈ pieces i → HasFDerivWithinAt f (f' x) (pieces i) x)
    (hf : ∀ i, InjOn f (pieces i))
    (J : ℝ) (hJ : ∀ i x, x ∈ pieces i → J ≤ |(f' x).det|)
    (V : ℝ≥0∞) (hV : ∀ i, μ (f '' pieces i) ≤ V) :
    ENNReal.ofReal J * μ S ≤ N * V := by
  calc
    ENNReal.ofReal J * μ S ≤ ENNReal.ofReal J * ∑ i, μ (pieces i) := by
      gcongr
      exact (measure_mono hcover).trans (measure_iUnion_fintype_le _ _)
    _ = ∑ i, ENNReal.ofReal J * μ (pieces i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i : Fin N, V := by
      apply Finset.sum_le_sum
      intro i hi
      exact (jacobian_mul_measure_le_image μ _ (hpieces i) f f' (hf' i) (hf i) J
        (hJ i)).trans (hV i)
    _ = N * V := by simp [nsmul_eq_mul]

end Submission.Obl.k4_quadratic_slope_volume
