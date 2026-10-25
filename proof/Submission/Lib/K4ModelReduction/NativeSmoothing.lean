import Submission.Lib.K4ModelReduction.RawSupport
import Submission.Lib.K4ModelReduction.RawIncidences

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Bounded selected incidence events for the native framework. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

def boundedRawIncidenceEvent {ι : Type*} (n : ℕ) (R δ : ℝ)
    (z : ι → EuclideanSpace ℝ (Fin 4)) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {p | p.1 ∈ rawSupport n R ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
    rawGraphPoint p.1 p.2 ∈ ⋃ i, ball (z i) (2 * δ)}

theorem measurableSet_boundedRawIncidenceEvent {ι : Type*}
    (n : ℕ) (R δ : ℝ) (z : ι → EuclideanSpace ℝ (Fin 4)) :
    MeasurableSet (boundedRawIncidenceEvent n R δ z) := by
  have hpoint : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => rawGraphPoint p.1 p.2) := by
    unfold rawGraphPoint
    fun_prop
  exact ((measurableSet_rawSupport n R).preimage measurable_fst).inter
    ((measurableSet_Icc.preimage measurable_snd).inter
      ((isOpen_iUnion fun i => isOpen_ball).measurableSet.preimage hpoint))

theorem boundedRawIncidenceEvent_subset {ι : Type*}
    (n : ℕ) (R δ : ℝ) (z : ι → EuclideanSpace ℝ (Fin 4)) :
    boundedRawIncidenceEvent n R δ z ⊆ rawSupport n R ×ˢ Icc (0 : ℝ) 1 :=
  fun _ hp => ⟨hp.1, hp.2.1⟩

theorem raw_smoothed_bounded_mass_lower_bound
    {n : ℕ} (b s : Fin n → EuclideanSpace ℝ (Fin 3)) (hn : 0 < n)
    {ι : Type*} (z : ι → EuclideanSpace ℝ (Fin 4)) (ρ : ι → ℝ)
    {δ R : ℝ} (hδ : 0 < δ) (hρ : ∀ i, ρ i ≤ δ)
    (hb : ∀ i, ‖b i‖ ≤ R) (hs : ∀ i, ‖s i‖ ≤ R) (c : ℝ≥0∞)
    (hmass : ∀ j, c ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      graphLift 0 (b j) + t • graphLift 1 (s j) ∈ ⋃ i, ball (z i) (ρ i)}) :
    c ≤ (rawSmoothedTrajectoryLaw b s δ).prod volume
      (boundedRawIncidenceEvent n (R + δ / 4) δ z) := by
  have := rawSmoothedTrajectoryLaw_isProbabilityMeasure b s hn hδ
  let H : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
    {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ rawGraphPoint p.1 p.2 ∈ ⋃ i, ball (z i) (2 * δ)}
  have hpoint : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => rawGraphPoint p.1 p.2) := by
    unfold rawGraphPoint
    fun_prop
  have hH : MeasurableSet H := (measurableSet_Icc.preimage measurable_snd).inter
    ((isOpen_iUnion fun i => isOpen_ball).measurableSet.preimage hpoint)
  have hprod : ((rawSmoothedTrajectoryLaw b s δ).prod (volume : Measure ℝ)).restrict
      (rawSupport n (R + δ / 4) ×ˢ univ) = (rawSmoothedTrajectoryLaw b s δ).prod volume := by
    rw [← Measure.prod_restrict, Measure.restrict_univ,
      rawSmoothedTrajectoryLaw_restrict_support b s hn hδ hb hs]
  calc
    c ≤ (rawSmoothedTrajectoryLaw b s δ).prod volume H :=
      raw_smoothed_selected_mass_lower_bound b s hn z ρ hδ hρ c hmass
    _ = ((rawSmoothedTrajectoryLaw b s δ).prod volume).restrict
        (rawSupport n (R + δ / 4) ×ˢ univ) H := by rw [hprod]
    _ = _ := by
      rw [Measure.restrict_apply hH]
      congr 1
      ext p
      change ((p.2 ∈ Icc (0 : ℝ) 1 ∧ rawGraphPoint p.1 p.2 ∈ ⋃ i, ball (z i) (2 * δ)) ∧
        (p.1 ∈ rawSupport n (R + δ / 4) ∧ True)) ↔
          (p.1 ∈ rawSupport n (R + δ / 4) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
            rawGraphPoint p.1 p.2 ∈ ⋃ i, ball (z i) (2 * δ))
      tauto

end Submission.Lib.K4ModelReduction
