import Submission.Lib.K4ModelReduction.TrajectorySmoothing

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-!
The two-dimensional intercept-density ceiling in Theorem 2.17. Integrating
one coordinate out of a small three-dimensional coefficient ball costs only
the length of that coordinate's interval.
-/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

/-- The two base-spatial coordinates, with the last spatial coordinate hidden. -/
def baseProjection (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i => x i.castSucc)

/-- Split spatial coordinates into the hidden scalar and observed base point. -/
def splitBase (x : EuclideanSpace ℝ (Fin 3)) : ℝ × EuclideanSpace ℝ (Fin 2) :=
  (x 2, baseProjection x)

theorem splitBase_measurePreserving : MeasurePreserving splitBase volume volume := by
  have h₁ := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)).comp
    (PiLp.volume_preserving_ofLp (Fin 3))
  have h₂ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin 2))
  have h := h₂.comp h₁
  convert h using 1
  funext x
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

theorem baseProjection_measurable : Measurable baseProjection :=
  splitBase_measurePreserving.measurable.snd

/-- Exact cylinder volume in the split spatial coordinates. -/
theorem base_cylinder_volume (a r : ℝ) (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : MeasurableSet S) :
    volume {x : EuclideanSpace ℝ (Fin 3) |
      x 2 ∈ Icc (a - r) (a + r) ∧ baseProjection x ∈ S} =
      ENNReal.ofReal (2 * r) * volume S := by
  change volume (splitBase ⁻¹' (Icc (a - r) (a + r) ×ˢ S)) = _
  rw [splitBase_measurePreserving.measure_preimage
    (measurableSet_Icc.prod hS).nullMeasurableSet]
  change ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (Icc (a - r) (a + r) ×ˢ S) = _
  rw [Measure.prod_prod, Real.volume_Icc]
  congr 2
  ring

/-- Projecting the smoothed intercept prior to its two observed coordinates
gives the ceiling `24/(π δ²)` relative to planar volume. -/
theorem coefficientBallLaw_base_bound (b : EuclideanSpace ℝ (Fin 3))
    {δ : ℝ} (hδ : 0 < δ) :
    (coefficientBallLaw b δ).map baseProjection ≤
      ENNReal.ofReal (24 / (Real.pi * δ ^ 2)) • volume := by
  apply Measure.le_iff.2
  intro S hS
  have hsubset : baseProjection ⁻¹' S ∩ ball b (δ / 4) ⊆
      {x : EuclideanSpace ℝ (Fin 3) |
        x 2 ∈ Icc (b 2 - δ / 4) (b 2 + δ / 4) ∧ baseProjection x ∈ S} := by
    rintro x ⟨hxS, hxb⟩
    have hcoord : |x 2 - b 2| ≤ δ / 4 := by
      calc
        |x 2 - b 2| = ‖(x - b) 2‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖x - b‖ := PiLp.norm_apply_le _ _
        _ ≤ δ / 4 := (by simpa only [mem_ball, dist_eq_norm] using hxb : ‖x - b‖ < δ / 4).le
    refine ⟨⟨?_, ?_⟩, hxS⟩ <;> linarith [(abs_le.mp hcoord).1, (abs_le.mp hcoord).2]
  have hvolume := (measure_mono hsubset).trans_eq (base_cylinder_volume (b 2) (δ / 4) S hS)
  rw [Measure.map_apply baseProjection_measurable hS, coefficientBallLaw_eq,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (hS.preimage baseProjection_measurable), Measure.smul_apply,
    smul_eq_mul]
  calc
    ENNReal.ofReal (48 / (Real.pi * δ ^ 3)) *
        volume (baseProjection ⁻¹' S ∩ ball b (δ / 4)) ≤
        ENNReal.ofReal (48 / (Real.pi * δ ^ 3)) *
          (ENNReal.ofReal (2 * (δ / 4)) * volume S) := mul_le_mul_right hvolume _
    _ = ENNReal.ofReal (24 / (Real.pi * δ ^ 2)) * volume S := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp
      ring

end Submission.Lib.K4ModelReduction
