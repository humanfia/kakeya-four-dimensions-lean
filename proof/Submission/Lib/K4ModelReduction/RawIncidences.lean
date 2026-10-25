import Submission.Lib.K4ModelReduction.RawCoefficients
import Submission.Lib.K4ModelReduction.GraphSmoothing

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 The retained incidence mass in the actual six-coordinate indexed prior. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

def rawGraphPoint (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

theorem rawGraphPoint_eq_lift (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    rawGraphPoint l t = graphLift 0 (coefficientPairEquiv l.2).1 +
      t • graphLift 1 (coefficientPairEquiv l.2).2 := by
  ext i
  fin_cases i
  · change t = 0 + t * 1
    ring
  · rfl
  · rfl
  · rfl

theorem raw_smoothed_selected_mass_lower_bound
    {n : ℕ} (b s : Fin n → EuclideanSpace ℝ (Fin 3)) (hn : 0 < n)
    {ι : Type*} (z : ι → EuclideanSpace ℝ (Fin 4)) (ρ : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hρ : ∀ i, ρ i ≤ δ) (c : ℝ≥0∞)
    (hmass : ∀ j, c ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      graphLift 0 (b j) + t • graphLift 1 (s j) ∈ ⋃ i, ball (z i) (ρ i)}) :
    c ≤ (rawSmoothedTrajectoryLaw b s δ).prod volume
      {p : (ℕ × (Fin 6 → ℝ)) × ℝ | p.2 ∈ Icc (0 : ℝ) 1 ∧
        rawGraphPoint p.1 p.2 ∈ ⋃ i, ball (z i) (2 * δ)} := by
  have := rawSmoothedTrajectoryLaw_isProbabilityMeasure b s hn hδ
  have := smoothedTrajectoryLaw_isProbabilityMeasure b s hn hδ
  let H : Set ((EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × ℝ) :=
    {p | p.2 ∈ Icc (0 : ℝ) 1 ∧
      graphLift 0 p.1.1 + p.2 • graphLift 1 p.1.2 ∈ ⋃ i, ball (z i) (2 * δ)}
  have hU : IsOpen (⋃ i, ball (z i) (2 * δ)) := isOpen_iUnion fun _ => isOpen_ball
  have hgraph : Continuous (fun p :
      (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × ℝ =>
        graphLift 0 p.1.1 + p.2 • graphLift 1 p.1.2) := by
    exact ((graphLift_continuous 0).comp (continuous_fst.comp continuous_fst)).add
      (continuous_snd.smul ((graphLift_continuous 1).comp (continuous_snd.comp continuous_fst)))
  have hH : MeasurableSet H :=
    (measurableSet_Icc.preimage measurable_snd).inter
      (hU.measurableSet.preimage hgraph.measurable)
  have hcoeff : Measurable (fun l : ℕ × (Fin 6 → ℝ) => coefficientPairEquiv l.2) :=
    coefficientPairEquiv.measurable.comp measurable_snd
  have hp : MeasurePreserving (fun l : ℕ × (Fin 6 → ℝ) => coefficientPairEquiv l.2)
      (rawSmoothedTrajectoryLaw b s δ) (smoothedTrajectoryLaw b s δ) :=
    ⟨hcoeff, rawSmoothedTrajectoryLaw_coefficients b s hδ⟩
  have hp' := hp.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hpre : (Prod.map (fun l : ℕ × (Fin 6 → ℝ) => coefficientPairEquiv l.2) id) ⁻¹' H =
      {p : (ℕ × (Fin 6 → ℝ)) × ℝ | p.2 ∈ Icc (0 : ℝ) 1 ∧
        rawGraphPoint p.1 p.2 ∈ ⋃ i, ball (z i) (2 * δ)} := by
    ext p
    change (p.2 ∈ Icc (0 : ℝ) 1 ∧
      graphLift 0 (coefficientPairEquiv p.1.2).1 +
        p.2 • graphLift 1 (coefficientPairEquiv p.1.2).2 ∈ ⋃ i, ball (z i) (2 * δ)) ↔
      (p.2 ∈ Icc (0 : ℝ) 1 ∧ rawGraphPoint p.1 p.2 ∈ ⋃ i, ball (z i) (2 * δ))
    rw [rawGraphPoint_eq_lift]
  have heq := hp'.measure_preimage hH.nullMeasurableSet
  rw [hpre] at heq
  rw [heq]
  exact smoothed_graph_selected_mass_lower_bound b s hn z ρ hδ hρ c hmass

end Submission.Lib.K4ModelReduction
