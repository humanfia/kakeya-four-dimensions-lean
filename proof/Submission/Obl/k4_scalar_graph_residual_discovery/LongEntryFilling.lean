/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file LongEntryFilling.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WholeStateFilling
import Submission.Obl.k4_scalar_graph_residual_discovery.StripPrior

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal NNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Lib.K4ContinuousKakeya
open Submission.Obl.k4_initial_horizon_bound

noncomputable section

/-- Earlier long durations and a final OLD-reference strip floor supply
the trajectory prior needed for actual GLOBAL physical filling. The
trajectory set is constructed, bounded and measured here. -/
theorem global_filling_of_long_original_entries
    (θ : Measure ScalarLine) [IsFiniteMeasure θ]
    (μ : Measure ScalarIncidence) [IsFiniteMeasure μ]
    {E R : Set ScalarIncidence} (hE : MeasurableSet E) (hR : MeasurableSet R) (hRE : R ⊆ E)
    {b p ρ H K C vsep L a δ : ℝ}
    (hb : 0 < b) (hp : 0 < p) (hbp : b ≤ p) (hp₁ : p ≤ 1) (hρ : 0 < ρ)
    (hH : 1 ≤ H) (hK : 0 < K) (hC : 0 ≤ C) (hMK : FiniteMK 2 C)
    (hvsep : 0 < vsep) (hL : 0 < L) (ha : 0 < a) (hδ : 0 < δ)
    (U : ℝ≥0) (hU : 3 * (U : ℝ) ≤ K) (hdom : μ.restrict R ≤ U • θ.prod volume)
    (hcoeff : ∀ z ∈ E, ∀ e, |z.1.2 e| ≤ H)
    (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hstates : ∀ S : Set (Fin 3 → ℤ), ∀ w : ℝ,
      ((μ.restrict R).restrict ((fun z => cell b (scalarPosition z)) ⁻¹' S))
        {z | |z.1.2 1 - w| ≤ vsep} ≤
          (1 / 2 : ℝ≥0∞) * (μ.restrict R) ((fun z => cell b (scalarPosition z)) ⁻¹' S))
    (S : Set (Fin 3 → ℤ))
    (hlong : ∀ z ∈ R, cell b (scalarPosition z) ∈ S → ENNReal.ofReal (a * ρ) ≤
      incidenceDuration (E ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) z.1)
    (hprod : (θ.prod volume) (E ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) ≤
      ENNReal.ofReal H * μ (E ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S))
    (hfloor : ENNReal.ofReal δ * μ (E ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) ≤
      μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S))
    (hpositive : μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) ≠ 0)
    (hpriorbudget : H / (a * δ) ≤ K)
    (hbudget : 200 * C * K ^ 4 * (1 + H) ^ 2 ≤ L * vsep) :
    (ρ / p) ^ 2 / L ≤
      (((fun z => cell p (assignedPosition b z)) ''
        (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S)).ncard : ℝ) := by
  have hstate : Measurable (fun z : ScalarIncidence => cell b (scalarPosition z)) :=
    measurable_cell b measurable_scalarPosition
  let oldEntry := E ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S
  have hOld : MeasurableSet oldEntry := hE.inter (hstate (to_countable S).measurableSet)
  let Λ := {l : ScalarLine | ENNReal.ofReal (a * ρ) ≤ incidenceDuration oldEntry l}
  have hΛ : MeasurableSet Λ := measurableSet_le measurable_const (measurable_incidenceDuration hOld)
  have hΛbound (l : ScalarLine) (hl : l ∈ Λ) : |l.2 0| ≤ H := by
    have hpos : incidenceDuration oldEntry l ≠ 0 :=
      ne_of_gt ((ENNReal.ofReal_pos.mpr (mul_pos ha hρ)).trans_le hl)
    obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero hpos
    exact hcoeff (l, t) ht.1 0
  have hprior : (θ Λ).toReal ≤
      K * (μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S)).toReal / ρ :=
    long_strip_prior_bound θ hOld Λ hΛ ha hρ hδ (by linarith : 0 ≤ H)
      (μ oldEntry) (μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S))
      (measure_ne_top μ _) (fun _ hl => hl) hprod hfloor hpriorbudget
  have hfinite := finite_original_physical_records R hH hb
    (fun z hz => hcoeff z (hRE hz)) (by
      intro z hz
      rw [abs_of_nonneg (htime z (hRE hz)).1]
      exact (htime z (hRE hz)).2)
  exact whole_state_planar_filling θ μ hR hb hp hbp hp₁ hρ hH hK hC hMK hvsep hL
    U hU hdom (fun z hz => hcoeff z (hRE hz)) (fun z hz => htime z (hRE hz)) hfinite
    hstates S Λ hΛ hΛbound hlong hpositive hprior hbudget

end

end Submission.Obl.k4_scalar_graph_residual_discovery
