import Submission.Lib.K4ModelReduction.RawFormat

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Pointwise coefficient support of the indexed smoothing prior. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

theorem rawSmoothedTrajectoryLaw_coefficient_bound {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ R : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) (hb : ∀ i, ‖b i‖ ≤ R) (hs : ∀ i, ‖s i‖ ≤ R) :
    ∀ᵐ l ∂rawSmoothedTrajectoryLaw b s δ, ∀ j, |l.2 j| ≤ R + δ / 4 := by
  have hGood : MeasurableSet {l : ℕ × (Fin 6 → ℝ) | ∀ j, |l.2 j| ≤ R + δ / 4} := by
    measurability
  rw [rawSmoothedTrajectoryLaw_eq_maps b s hn hδ]
  apply ae_finsetSum_measure_iff.mpr
  intro i _
  apply Measure.ae_smul_measure
  have hmk : Measurable (Prod.mk (i : ℕ) : (Fin 6 → ℝ) → ℕ × (Fin 6 → ℝ)) :=
    measurable_const.prodMk measurable_id
  apply (ae_map_iff hmk.aemeasurable hGood).2
  have hA : MeasurableSet (coefficientPairEquiv ⁻¹'
      (ball (b i) (δ / 4) ×ˢ ball (s i) (δ / 4))) :=
    (measurableSet_ball.prod measurableSet_ball).preimage coefficientPairEquiv.measurable
  filter_upwards [ae_restrict_mem hA] with x hx
  exact rawCoefficientRegion_bound (b i) (s i) (hb i) (hs i) hx

def rawSupport (n : ℕ) (R : ℝ) : Set (ℕ × (Fin 6 → ℝ)) :=
  {l | l.1 < n ∧ ∀ j, |l.2 j| ≤ R}

theorem measurableSet_rawSupport (n : ℕ) (R : ℝ) : MeasurableSet (rawSupport n R) := by
  unfold rawSupport
  measurability

theorem rawSmoothedTrajectoryLaw_support {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ R : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) (hb : ∀ i, ‖b i‖ ≤ R) (hs : ∀ i, ‖s i‖ ≤ R) :
    ∀ᵐ l ∂rawSmoothedTrajectoryLaw b s δ, l ∈ rawSupport n (R + δ / 4) := by
  filter_upwards [rawSmoothedTrajectoryLaw_label_bound b s hδ,
    rawSmoothedTrajectoryLaw_coefficient_bound b s hn hδ hb hs] with l hl hbound
  exact ⟨hl, hbound⟩

theorem rawSmoothedTrajectoryLaw_restrict_support {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ R : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) (hb : ∀ i, ‖b i‖ ≤ R) (hs : ∀ i, ‖s i‖ ≤ R) :
    (rawSmoothedTrajectoryLaw b s δ).restrict (rawSupport n (R + δ / 4)) =
      rawSmoothedTrajectoryLaw b s δ :=
  Measure.restrict_eq_self_of_ae_mem (rawSmoothedTrajectoryLaw_support b s hn hδ hb hs)

end Submission.Lib.K4ModelReduction
