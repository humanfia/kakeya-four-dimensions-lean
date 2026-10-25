import Submission.Lib.K4ModelReduction.TrajectorySmoothing

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Keeping the original discrete label in a smoothed coefficient prior. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable def indexedMixture {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Fin n → Measure X) : Measure (ℕ × X) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, (Measure.dirac (i : ℕ)).prod (μ i)

theorem indexedMixture_isProbabilityMeasure {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (hn : 0 < n) :
    IsProbabilityMeasure (indexedMixture μ) := by
  constructor
  simp only [indexedMixture, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply, measure_univ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)

theorem indexedMixture_marginal {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)] :
    (indexedMixture μ).map Prod.snd = (n : ℝ≥0∞)⁻¹ • ∑ i, μ i := by
  rw [indexedMixture, Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_finset_sum' measurable_snd.aemeasurable]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact measurePreserving_snd.map_eq

theorem indexedMixture_label_bound {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Fin n → Measure X) [∀ i, SFinite (μ i)] :
    indexedMixture μ {z | n ≤ z.1} = 0 := by
  have hS : MeasurableSet {z : ℕ × X | n ≤ z.1} := by measurability
  have hzero (i : Fin n) : (Measure.dirac (i : ℕ)).prod (μ i) {z | n ≤ z.1} = 0 := by
    have hmk : Measurable (Prod.mk (i : ℕ) : X → ℕ × X) :=
      measurable_const.prodMk measurable_id
    rw [Measure.dirac_prod, Measure.map_apply hmk hS]
    have hempty : (Prod.mk (i : ℕ)) ⁻¹' {z : ℕ × X | n ≤ z.1} = ∅ := by
      ext x
      simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_le_of_gt i.isLt
    rw [hempty, measure_empty]
  simp only [indexedMixture, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    hzero, Finset.sum_const_zero, mul_zero]

theorem dirac_prod_restrict_count {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (i : ℕ) (S : Set X) :
    (Measure.dirac i).prod (μ.restrict S) =
      ((Measure.count : Measure ℕ).prod μ).restrict ({i} ×ˢ S) := by
  rw [← Measure.prod_restrict, Measure.restrict_singleton]
  simp

/-- The indexed law has exactly the finite labeled-volume form used by
the framework whenever its component laws do. -/
theorem indexedMixture_eq_restrictions {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Fin n → Measure X) (ν : Measure X) [SFinite ν]
    (a : Fin n → ℝ≥0∞) (S : Fin n → Set X)
    (hμ : ∀ i, μ i = a i • ν.restrict (S i)) :
    indexedMixture μ = ∑ i, ((n : ℝ≥0∞)⁻¹ * a i) •
      ((Measure.count : Measure ℕ).prod ν).restrict ({(i : ℕ)} ×ˢ S i) := by
  simp only [indexedMixture, Finset.smul_sum, hμ, Measure.prod_smul_right,
    smul_smul, dirac_prod_restrict_count]

noncomputable def indexedSmoothedTrajectoryLaw {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    Measure (ℕ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) :=
  indexedMixture fun i => (coefficientBallLaw (b i) δ).prod (coefficientBallLaw (s i) δ)

theorem indexedSmoothedTrajectoryLaw_isProbabilityMeasure {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    IsProbabilityMeasure (indexedSmoothedTrajectoryLaw b s δ) := by
  have : ∀ i, IsProbabilityMeasure (coefficientBallLaw (b i) δ) :=
    fun i => coefficientBallLaw_isProbabilityMeasure _ hδ
  have : ∀ i, IsProbabilityMeasure (coefficientBallLaw (s i) δ) :=
    fun i => coefficientBallLaw_isProbabilityMeasure _ hδ
  exact indexedMixture_isProbabilityMeasure _ hn

theorem indexedSmoothedTrajectoryLaw_marginal {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 < δ) :
    (indexedSmoothedTrajectoryLaw b s δ).map Prod.snd = smoothedTrajectoryLaw b s δ := by
  have : ∀ i, IsProbabilityMeasure (coefficientBallLaw (b i) δ) :=
    fun i => coefficientBallLaw_isProbabilityMeasure _ hδ
  have : ∀ i, IsProbabilityMeasure (coefficientBallLaw (s i) δ) :=
    fun i => coefficientBallLaw_isProbabilityMeasure _ hδ
  exact indexedMixture_marginal _

theorem coefficientBallLaw_prod_eq (b s : EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    (coefficientBallLaw b δ).prod (coefficientBallLaw s δ) =
      ENNReal.ofReal (48 / (Real.pi * δ ^ 3)) ^ 2 •
        volume.restrict (ball b (δ / 4) ×ˢ ball s (δ / 4)) := by
  rw [coefficientBallLaw_eq, coefficientBallLaw_eq, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul, Measure.prod_restrict, pow_two]
  rfl

theorem indexedSmoothedTrajectoryLaw_eq {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    indexedSmoothedTrajectoryLaw b s δ =
      ∑ i : Fin n, ((n : ℝ≥0∞)⁻¹ * ENNReal.ofReal (48 / (Real.pi * δ ^ 3)) ^ 2) •
        ((Measure.count : Measure ℕ).prod volume).restrict
          ({(i : ℕ)} ×ˢ (ball (b i) (δ / 4) ×ˢ ball (s i) (δ / 4))) :=
  indexedMixture_eq_restrictions _ volume _ _ (fun _ => coefficientBallLaw_prod_eq _ _ _)

theorem indexedSmoothedTrajectoryLaw_label_bound {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ z ∂indexedSmoothedTrajectoryLaw b s δ, z.1 < n := by
  have : ∀ i, IsProbabilityMeasure (coefficientBallLaw (b i) δ) :=
    fun i => coefficientBallLaw_isProbabilityMeasure _ hδ
  have : ∀ i, IsProbabilityMeasure (coefficientBallLaw (s i) δ) :=
    fun i => coefficientBallLaw_isProbabilityMeasure _ hδ
  rw [ae_iff]
  simpa only [indexedSmoothedTrajectoryLaw, not_lt] using indexedMixture_label_bound
    (fun i => (coefficientBallLaw (b i) δ).prod (coefficientBallLaw (s i) δ))

theorem indexedSmoothedTrajectoryLaw_slope {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    (indexedSmoothedTrajectoryLaw b s δ).map (fun z => z.2.2) = smoothedSlopeLaw s δ := by
  change (indexedSmoothedTrajectoryLaw b s δ).map (Prod.snd ∘ Prod.snd) = _
  rw [← Measure.map_map measurable_snd measurable_snd,
    indexedSmoothedTrajectoryLaw_marginal b s hδ,
    smoothedTrajectoryLaw_slope b s hn hδ]

end Submission.Lib.K4ModelReduction
