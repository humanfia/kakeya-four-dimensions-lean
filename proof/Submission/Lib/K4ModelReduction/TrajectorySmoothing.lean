import Submission.Lib.K4ModelReduction.SlopeSmoothing

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-!
The product prior on perturbed intercept and slope coefficients. Its
normalization is independent of the successful trajectory-time incidences.
-/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

/-- Uniform probability on a small ball in coefficient space. -/
noncomputable def coefficientBallLaw (x : EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin 3)) :=
  smoothedSlopeLaw (fun _ : Fin 1 => x) δ

theorem coefficientBallLaw_eq (x : EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    coefficientBallLaw x δ = ENNReal.ofReal (48 / (Real.pi * δ ^ 3)) •
      volume.restrict (ball x (δ / 4)) := by
  simp [coefficientBallLaw, smoothedSlopeLaw]

theorem coefficientBallLaw_isProbabilityMeasure (x : EuclideanSpace ℝ (Fin 3))
    {δ : ℝ} (hδ : 0 < δ) : IsProbabilityMeasure (coefficientBallLaw x δ) :=
  smoothedSlopeLaw_isProbabilityMeasure _ (by norm_num) hδ

theorem coefficientBallLaw_ae_mem (x : EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    ∀ᵐ y ∂coefficientBallLaw x δ, y ∈ ball x (δ / 4) := by
  rw [coefficientBallLaw_eq]
  apply ae_iff.2
  change (ENNReal.ofReal (48 / (Real.pi * δ ^ 3)) •
    volume.restrict (ball x (δ / 4))) (ball x (δ / 4))ᶜ = 0
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_ball.compl]
  simp

/-- First choose an original indexed trajectory uniformly, then perturb its
intercept and slope independently. -/
noncomputable def smoothedTrajectoryLaw {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, (coefficientBallLaw (b i) δ).prod (coefficientBallLaw (s i) δ)

theorem smoothedTrajectoryLaw_isProbabilityMeasure {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) : IsProbabilityMeasure (smoothedTrajectoryLaw b s δ) := by
  have : ∀ i, IsProbabilityMeasure (coefficientBallLaw (b i) δ) :=
    fun i => coefficientBallLaw_isProbabilityMeasure _ hδ
  have : ∀ i, IsProbabilityMeasure (coefficientBallLaw (s i) δ) :=
    fun i => coefficientBallLaw_isProbabilityMeasure _ hδ
  constructor
  simp only [smoothedTrajectoryLaw, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply, measure_univ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)

/-- The full slope marginal is precisely the smoothed law whose density was
bounded using direction separation. Conditioning on incidence success has
not entered this calculation. -/
theorem smoothedTrajectoryLaw_slope {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) :
    (smoothedTrajectoryLaw b s δ).map Prod.snd = smoothedSlopeLaw s δ := by
  have : ∀ i, IsProbabilityMeasure (coefficientBallLaw (b i) δ) :=
    fun i => coefficientBallLaw_isProbabilityMeasure _ hδ
  have : ∀ i, IsProbabilityMeasure (coefficientBallLaw (s i) δ) :=
    fun i => coefficientBallLaw_isProbabilityMeasure _ hδ
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcoef : (n : ℝ≥0∞)⁻¹ * ENNReal.ofReal (48 / (Real.pi * δ ^ 3)) =
      ENNReal.ofReal (48 / ((n : ℝ) * Real.pi * δ ^ 3)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hnreal,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [smoothedTrajectoryLaw, Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_finset_sum' measurable_snd.aemeasurable]
  have hmap (i : Fin n) :
      ((coefficientBallLaw (b i) δ).prod (coefficientBallLaw (s i) δ)).map Prod.snd =
        coefficientBallLaw (s i) δ := measurePreserving_snd.map_eq
  simp_rw [hmap, coefficientBallLaw_eq]
  rw [← Finset.smul_sum, smul_smul, hcoef]
  rfl

end Submission.Lib.K4ModelReduction
