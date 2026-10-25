-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.ProjectionMeasure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Geometry

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

lemma measurePreserving_coordinates :
    MeasurePreserving (fun p : Space => (p 0, (p 1, p 2))) := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_finTwoArrow ℝ)).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
        (PiLp.volume_preserving_ofLp (Fin 3)))
  convert h using 1
  funext p
  rfl

lemma measurePreserving_projection_fiber {f : ℝ → ℝ} (hf : Measurable f) (b d : ℝ) :
    MeasurePreserving (fun p : Space => (projection f p, p 1 - (b + d * p 2))) := by
  have h₀ : MeasurePreserving (fun p : Space => ((p 1, p 2), p 0)) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (ℝ × ℝ)))).comp
      measurePreserving_coordinates
  have h₁ : MeasurePreserving (fun q : (ℝ × ℝ) × ℝ =>
      (q.1, q.2 + f q.1.2 * q.1.1)) := by
    change MeasurePreserving _ (volume.prod volume) (volume.prod volume)
    apply (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).skew_product
      (g := fun q : ℝ × ℝ => fun a : ℝ => a + f q.2 * q.1)
    · exact measurable_snd.add ((hf.comp (measurable_snd.comp measurable_fst)).mul
        (measurable_fst.comp measurable_fst))
    · exact Filter.Eventually.of_forall fun q =>
        (measurePreserving_add_right (volume : Measure ℝ) (f q.2 * q.1)).map_eq
  have h₂ : MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => ((q.2, q.1.2), q.1.1)) := by
    have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (ℝ × ℝ)))).comp
      (((MeasurePreserving.id (volume : Measure ℝ)).prod
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ)))).comp
          (measurePreserving_prodAssoc (volume : Measure ℝ) volume volume))
    convert h using 1
    rfl
  have h₃ : MeasurePreserving (fun q : (ℝ × ℝ) × ℝ =>
      (q.1, q.2 - (b + d * q.1.2))) := by
    change MeasurePreserving _ (volume.prod volume) (volume.prod volume)
    apply (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).skew_product
      (g := fun q : ℝ × ℝ => fun a : ℝ => a - (b + d * q.2))
    · exact measurable_snd.sub (measurable_const.add
        (measurable_const.mul (measurable_snd.comp measurable_fst)))
    · exact Filter.Eventually.of_forall fun q =>
        (measurePreserving_sub_right (volume : Measure ℝ) (b + d * q.2)).map_eq
  exact h₃.comp (h₂.comp (h₁.comp h₀))

/-- Every transverse tube has projection fibers of length at most `6 * δ`.
The image need not be measurable: its outer volume appears on the right. -/
theorem volume_le_projection_volume {f : ℝ → ℝ} (hf : Measurable f)
    {δ : ℝ} (_hδ : 0 < δ) {x v : Space} (hv : ‖v‖ = 1)
    (htrans : (1 / 2 : ℝ) ≤ |v 2|) {Y : Set Space} (hY : Y ⊆ Tube δ x v) :
    volume Y ≤ ENNReal.ofReal (6 * δ) * volume (projection f '' Y) := by
  let A := toMeasurable volume (projection f '' Y)
  let Φ : Space → (ℝ × ℝ) × ℝ := fun p =>
    (projection f p, p 1 - (intercept x v 1 + slope v 1 * p 2))
  have hΦ : MeasurePreserving Φ := measurePreserving_projection_fiber hf _ _
  have hA : MeasurableSet A := measurableSet_toMeasurable _ _
  have hsub : Y ⊆ Φ ⁻¹' (A ×ˢ Icc (-3 * δ) (3 * δ)) := by
    intro p hp
    refine ⟨subset_toMeasurable volume (projection f '' Y) (mem_image_of_mem _ hp), ?_⟩
    have h := abs_lt.mp (tube_coordinate_bound hv htrans (hY hp) 1)
    exact ⟨by linarith [h.1], h.2.le⟩
  calc
    volume Y ≤ volume (Φ ⁻¹' (A ×ˢ Icc (-3 * δ) (3 * δ))) := measure_mono hsub
    _ = volume (A ×ˢ Icc (-3 * δ) (3 * δ)) :=
      hΦ.measure_preimage (hA.prod measurableSet_Icc).nullMeasurableSet
    _ = volume A * ENNReal.ofReal (6 * δ) := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
      congr 2
      ring
    _ = ENNReal.ofReal (6 * δ) * volume (projection f '' Y) := by
      rw [show volume A = volume (projection f '' Y) from measure_toMeasurable _]
      exact mul_comm _ _

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
