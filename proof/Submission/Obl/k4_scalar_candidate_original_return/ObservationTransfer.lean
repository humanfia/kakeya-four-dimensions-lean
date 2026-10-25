import Submission.Obl.k4_scalar_candidate_original_return.ObservationMarginal

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set

noncomputable section

def fullSourceCoordinates (q : Inc) : Fin 6 → ℝ := observationShear (q.1.2, q.2)

lemma measurable_fullSourceCoordinates : Measurable fullSourceCoordinates :=
  observationShear.measurable.comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- An exact selected source law gives the original terminal-observation law. -/
theorem originalObservation_law_of_source (δ : ℝ) (μ : Measure Inc)
    {f : (Fin 6 → ℝ) → ℝ} (hf : Measurable f) (hfi : Integrable f volume)
    (hf0 : ∀ w, 0 ≤ f w)
    (hsource : μ.map fullSourceCoordinates = volume.withDensity (fun w => ENNReal.ofReal (f w))) :
    μ.map (originalObservation δ) = ((volume : Measure Base).prod Measure.count).withDensity
      (fun z => ENNReal.ofReal (scalarMarginal δ f z)) := by
  have hmap : originalObservation δ = rawObservation δ ∘ fullSourceCoordinates := by
    funext q
    exact originalObservation_in_coordinates δ q
  rw [hmap, ← Measure.map_map (measurable_rawObservation δ)
    measurable_fullSourceCoordinates, hsource]
  exact map_rawObservation_withDensity δ hf hfi hf0

/-- Success under a selected original law is exactly the success integral of
its explicit terminal-observation density. -/
theorem original_observation_mass (δ : ℝ) (μ : Measure Inc) (C : Set Inc)
    {f : (Fin 6 → ℝ) → ℝ} (hf : Measurable f) (hfi : Integrable f volume)
    (hf0 : ∀ w, 0 ≤ f w)
    (hsource : (μ.restrict C).map fullSourceCoordinates =
      volume.withDensity (fun w => ENNReal.ofReal (f w)))
    (S : Set (Base × ℤ)) (hS : MeasurableSet S) :
    μ {q | q ∈ C ∧ originalObservation δ q ∈ S} =
      ∫⁻ z, S.indicator (fun z => ENNReal.ofReal (scalarMarginal δ f z)) z
        ∂(volume : Measure Base).prod Measure.count := by
  rw [lintegral_indicator hS]
  calc
    _ = (μ.restrict C) (originalObservation δ ⁻¹' S) := by
      rw [Measure.restrict_apply (hS.preimage (measurable_originalObservation δ))]
      congr 1
      ext q
      exact and_comm
    _ = ((μ.restrict C).map (originalObservation δ)) S :=
      (Measure.map_apply (measurable_originalObservation δ) hS).symm
    _ = (((volume : Measure Base).prod Measure.count).withDensity
        (fun z => ENNReal.ofReal (scalarMarginal δ f z))) S := by
      rw [originalObservation_law_of_source δ (μ.restrict C) hf hfi hf0 hsource]
    _ = _ := withDensity_apply _ hS

end

end Submission.Obl.k4_scalar_candidate_original_return
