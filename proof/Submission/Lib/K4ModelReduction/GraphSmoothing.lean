import Submission.Lib.K4ModelReduction.GraphCoordinates
import Submission.Lib.K4ModelReduction.Perturbation
import Submission.Lib.K4ModelReduction.TrajectorySmoothing

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-! Preservation of the incidence mass by the actual finite graph-family prior. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

/-- The time coordinate of the intercept remains zero, and that of the
direction remains one, throughout coefficient smoothing. -/
def liftCoefficientPair (l : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) :=
  (graphLift 0 l.1, graphLift 1 l.2)

theorem liftCoefficientPair_continuous : Continuous liftCoefficientPair :=
  ((graphLift_continuous 0).comp continuous_fst).prodMk
    ((graphLift_continuous 1).comp continuous_snd)

theorem graph_component_selected_mass_lower_bound
    {ι : Type*} (z : ι → EuclideanSpace ℝ (Fin 4)) (ρ : ι → ℝ)
    (b s : EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 < δ)
    (hρ : ∀ i, ρ i ≤ δ) (c : ℝ≥0∞)
    (hmass : c ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      graphLift 0 b + t • graphLift 1 s ∈ ⋃ i, ball (z i) (ρ i)}) :
    c ≤ ((coefficientBallLaw b δ).prod (coefficientBallLaw s δ)).prod volume
      {p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × ℝ |
        p.2 ∈ Icc (0 : ℝ) 1 ∧
        graphLift 0 p.1.1 + p.2 • graphLift 1 p.1.2 ∈ ⋃ i, ball (z i) (2 * δ)} := by
  have : IsProbabilityMeasure (coefficientBallLaw b δ) :=
    coefficientBallLaw_isProbabilityMeasure _ hδ
  have : IsProbabilityMeasure (coefficientBallLaw s δ) :=
    coefficientBallLaw_isProbabilityMeasure _ hδ
  let μ := (coefficientBallLaw b δ).prod (coefficientBallLaw s δ)
  have hprod : ∀ᵐ l ∂μ, l ∈ ball b (δ / 4) ×ˢ ball s (δ / 4) := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_ball.prod measurableSet_ball)).2
    filter_upwards [coefficientBallLaw_ae_mem b δ] with b' hb'
    filter_upwards [coefficientBallLaw_ae_mem s δ] with s' hs'
    exact ⟨hb', hs'⟩
  have hnear : ∀ᵐ l ∂μ.map liftCoefficientPair,
      dist l.1 (graphLift 0 b) ≤ δ / 4 ∧ dist l.2 (graphLift 1 s) ≤ δ / 4 := by
    apply (ae_map_iff liftCoefficientPair_continuous.measurable.aemeasurable
      ((measurableSet_le (measurable_fst.dist measurable_const) measurable_const).inter
        (measurableSet_le (measurable_snd.dist measurable_const) measurable_const))).2
    filter_upwards [hprod] with l hl
    change dist (graphLift 0 l.1) (graphLift 0 b) ≤ δ / 4 ∧
      dist (graphLift 1 l.2) (graphLift 1 s) ≤ δ / 4
    rw [(graphLift_isometry 0).dist_eq, (graphLift_isometry 1).dist_eq]
    exact ⟨(mem_ball.mp hl.1).le, (mem_ball.mp hl.2).le⟩
  have hbound := smoothed_selected_mass_lower_bound z ρ hδ hρ
    (μ.map liftCoefficientPair) c hnear hmass
  have hU : IsOpen (⋃ i, ball (z i) (2 * δ)) := isOpen_iUnion fun _ => isOpen_ball
  have hmap : Continuous (fun p :
      (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) × ℝ =>
      p.1.1 + p.2 • p.1.2) := by fun_prop
  have hE : MeasurableSet {p :
      (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) × ℝ |
      p.2 ∈ Icc (0 : ℝ) 1 ∧ p.1.1 + p.2 • p.1.2 ∈ ⋃ i, ball (z i) (2 * δ)} :=
    (measurableSet_Icc.preimage measurable_snd).inter
      (hU.measurableSet.preimage hmap.measurable)
  have hprodmap : (μ.map liftCoefficientPair).prod volume =
      (μ.prod (volume : Measure ℝ)).map (Prod.map liftCoefficientPair id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map μ (volume : Measure ℝ)
      liftCoefficientPair_continuous.measurable measurable_id
  rw [hprodmap, Measure.map_apply
    (liftCoefficientPair_continuous.measurable.prodMap measurable_id) hE] at hbound
  exact hbound

/-- The uniformly sampled, independently perturbed finite graph family
retains the common time-mass lower bound in the enlarged cover. -/
theorem smoothed_graph_selected_mass_lower_bound
    {n : ℕ} (b s : Fin n → EuclideanSpace ℝ (Fin 3)) (hn : 0 < n)
    {ι : Type*} (z : ι → EuclideanSpace ℝ (Fin 4)) (ρ : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hρ : ∀ i, ρ i ≤ δ) (c : ℝ≥0∞)
    (hmass : ∀ j, c ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      graphLift 0 (b j) + t • graphLift 1 (s j) ∈ ⋃ i, ball (z i) (ρ i)}) :
    c ≤ (smoothedTrajectoryLaw b s δ).prod volume
      {p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × ℝ |
        p.2 ∈ Icc (0 : ℝ) 1 ∧
        graphLift 0 p.1.1 + p.2 • graphLift 1 p.1.2 ∈ ⋃ i, ball (z i) (2 * δ)} := by
  have hsumprod : (∑ j, (coefficientBallLaw (b j) δ).prod (coefficientBallLaw (s j) δ)).prod
      (volume : Measure ℝ) =
      ∑ j, ((coefficientBallLaw (b j) δ).prod (coefficientBallLaw (s j) δ)).prod volume := by
    rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  rw [smoothedTrajectoryLaw, Measure.prod_smul_left, hsumprod,
    Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  calc
    c = (n : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) * c) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hn0 (by simp), one_mul]
    _ ≤ _ := by
      apply mul_le_mul_right
      have hsum := Finset.sum_le_sum (fun (j : Fin n) (_ : j ∈ Finset.univ) =>
        graph_component_selected_mass_lower_bound z ρ (b j) (s j) hδ hρ c (hmass j))
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum

end Submission.Lib.K4ModelReduction
