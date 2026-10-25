/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeComparisonFrames.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.ObservedPairs
import Submission.Obl.k4_horizontal_strict_parameter_step.NativePredictor
import Submission.Obl.k4_horizontal_strict_parameter_step.ComparisonCoordinates

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory

noncomputable section

structure ComparisonFrame where
  velocity : ℝ
  timeCenter : ℝ
  timeScale : ℝ
  pCenter : ℝ
  qCenter : ℝ
  parameterScale : ℝ

namespace ComparisonFrame

def coordinates (r : ComparisonFrame) : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3) :=
  comparisonCoordinates r.velocity r.timeCenter r.timeScale r.pCenter r.qCenter r.parameterScale

def rechart (r : ComparisonFrame) (h : Fin 6 → ℝ) : Fin 6 → ℝ :=
  predictorRechart h r.timeCenter r.timeScale r.pCenter r.qCenter r.parameterScale

theorem rechart_coordinates (r : ComparisonFrame) (h : Fin 6 → ℝ) (z : Fin 3 → ℝ)
    (hH : r.timeScale ≠ 0) (hD : r.parameterScale ≠ 0) :
    predictor (r.rechart h) (r.coordinates z 0) (r.coordinates z 1) (r.coordinates z 2) =
      predictor h (z 0) (reconstructBase r.velocity z 1) (reconstructBase r.velocity z 2) := by
  rw [rechart, predictor_rechart]
  change predictor h
    (r.timeCenter + r.timeScale * ((z 0 - r.timeCenter) / r.timeScale))
    (r.pCenter + r.parameterScale *
      ((reconstructBase r.velocity z 1 - r.pCenter) / r.parameterScale))
    (r.qCenter + r.parameterScale *
      ((reconstructBase r.velocity z 2 - r.qCenter) / r.parameterScale)) = _
  congr 1 <;> field_simp [hH, hD] <;> ring

def markedCoordinates {ι : Type*} (r : ι → ComparisonFrame)
    (p : ι × (Fin 3 → ℝ)) : EuclideanSpace ℝ (Fin 3) :=
  (r p.1).coordinates p.2

theorem measurable_markedCoordinates {ι : Type*} [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (r : ι → ComparisonFrame) :
    Measurable (markedCoordinates r) := by
  apply measurable_from_prod_countable_right
  intro i
  change Measurable ((r i).coordinates)
  exact measurable_comparisonCoordinates (r i).velocity (r i).timeCenter (r i).timeScale
    (r i).pCenter (r i).qCenter (r i).parameterScale

/-- A static time-parameter point in the normalized comparison chart. -/
def parameterPoint (r : ComparisonFrame) (t p q : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(t - r.timeCenter) / r.timeScale,
    (p - r.pCenter) / r.parameterScale, (q - r.qCenter) / r.parameterScale]

theorem rechart_parameterPoint (r : ComparisonFrame) (h : Fin 6 → ℝ) (t p q : ℝ)
    (hH : r.timeScale ≠ 0) (hD : r.parameterScale ≠ 0) :
    predictor (r.rechart h) (r.parameterPoint t p q 0) (r.parameterPoint t p q 1)
      (r.parameterPoint t p q 2) = predictor h t p q := by
  rw [rechart, predictor_rechart]
  change predictor h (r.timeCenter + r.timeScale * ((t - r.timeCenter) / r.timeScale))
    (r.pCenter + r.parameterScale * ((p - r.pCenter) / r.parameterScale))
    (r.qCenter + r.parameterScale * ((q - r.qCenter) / r.parameterScale)) = _
  congr 1 <;> field_simp [hH, hD] <;> ring

theorem parameterPoint_mem_half (r : ComparisonFrame) {t p q : ℝ}
    (hH : 0 < r.timeScale) (hD : 0 < r.parameterScale)
    (ht : |t - r.timeCenter| ≤ r.timeScale / 4)
    (hp : |p - r.pCenter| ≤ r.parameterScale / 4)
    (hq : |q - r.qCenter| ≤ r.parameterScale / 4) :
    ‖r.parameterPoint t p q‖ ≤ 1 / 2 := by
  apply norm_fin3_le_half
  intro i
  fin_cases i
  · change |(t - r.timeCenter) / r.timeScale| ≤ (1 : ℝ) / 4
    rw [abs_div, abs_of_pos hH, div_le_iff₀ hH]
    linarith
  · change |(p - r.pCenter) / r.parameterScale| ≤ (1 : ℝ) / 4
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    linarith
  · change |(q - r.qCenter) / r.parameterScale| ≤ (1 : ℝ) / 4
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    linarith

/-- A half-ball comparison controls the entire padded old product domain.
This return costs no additional polynomial norm extension. -/
theorem product_comparison (r : ComparisonFrame) (f h : Fin 6 → ℝ) {t p q M : ℝ}
    (hH : 0 < r.timeScale) (hD : 0 < r.parameterScale)
    (ht : |t - r.timeCenter| ≤ r.timeScale / 4)
    (hp : |p - r.pCenter| ≤ r.parameterScale / 4)
    (hq : |q - r.qCenter| ≤ r.parameterScale / 4)
    (hcomp : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 2 →
      |predictor (r.rechart f) (z 0) (z 1) (z 2) -
        predictor (r.rechart h) (z 0) (z 1) (z 2)| ≤ M) :
    |predictor f t p q - predictor h t p q| ≤ M := by
  have hh := hcomp (r.parameterPoint t p q) (r.parameterPoint_mem_half hH hD ht hp hq)
  rwa [r.rechart_parameterPoint f t p q hH.ne' hD.ne',
    r.rechart_parameterPoint h t p q hH.ne' hD.ne'] at hh

end ComparisonFrame

namespace ObservedPairs

variable {Ω Γ J : Type*} [MeasurableSpace Ω] [DecidableEq Γ] [DecidableEq J]
  {m n : ℕ} {S : Set Ω} {A : Fin m → Set Ω} {B : Fin n → Set Ω}
  (T : ObservedPairs S A B) (group : Fin m → Γ) (block : Fin n → J)
  (frame : Γ × J → ComparisonFrame)

def markedFrame (i : Fin T.count) : ComparisonFrame :=
  frame (group (T.old i), block (T.native i))

/-- The two sides of the actual observed comparison use the same colour frame:
old full-time coefficients on the source side, true affine coefficients on witnesses. -/
def comparisonPredictors (old : Fin m → Fin 6 → ℝ) (native : Fin n → Fin 4 → ℝ) :
    T.Index group block → Fin 6 → ℝ
  | Sum.inl i => (frame (group i.val.1, i.val.2)).rechart (old i.val.1)
  | Sum.inr i => (frame (i.val.2, block i.val.1)).rechart
      (affinePredictor (native i.val.1) (frame (i.val.2, block i.val.1)).velocity)

theorem source_evaluation (old : Fin m → Fin 6 → ℝ) (native : Fin n → Fin 4 → ℝ)
    (i : Fin T.count) (z : Fin 3 → ℝ)
    (hH : (T.markedFrame group block frame i).timeScale ≠ 0)
    (hD : (T.markedFrame group block frame i).parameterScale ≠ 0) :
    predictor (T.comparisonPredictors group block frame old native (T.source group block i))
      ((T.markedFrame group block frame i).coordinates z 0)
      ((T.markedFrame group block frame i).coordinates z 1)
      ((T.markedFrame group block frame i).coordinates z 2) =
    predictor (old (T.old i)) (z 0)
      (reconstructBase (T.markedFrame group block frame i).velocity z 1)
      (reconstructBase (T.markedFrame group block frame i).velocity z 2) :=
  ComparisonFrame.rechart_coordinates _ _ _ hH hD

theorem witness_evaluation (old : Fin m → Fin 6 → ℝ) (native : Fin n → Fin 4 → ℝ)
    (i : Fin T.count) (z : Fin 3 → ℝ)
    (hH : (T.markedFrame group block frame i).timeScale ≠ 0)
    (hD : (T.markedFrame group block frame i).parameterScale ≠ 0) :
    predictor (T.comparisonPredictors group block frame old native (T.witness group block i))
      ((T.markedFrame group block frame i).coordinates z 0)
      ((T.markedFrame group block frame i).coordinates z 1)
      ((T.markedFrame group block frame i).coordinates z 2) =
    predictor (affinePredictor (native (T.native i))
      (T.markedFrame group block frame i).velocity) (z 0)
      (reconstructBase (T.markedFrame group block frame i).velocity z 1)
      (reconstructBase (T.markedFrame group block frame i).velocity z 2) :=
  ComparisonFrame.rechart_coordinates _ _ _ hH hD

end ObservedPairs

end

end Submission.Obl.k4_horizontal_strict_parameter_step
