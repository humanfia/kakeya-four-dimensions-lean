import Submission.Obl.k4_scalar_candidate_original_return.CoordinateFormat

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set

noncomputable section

/-- Forget only the discrete line copy and use the volume-preserving scalar shear. -/
def sourceCoordinates (q : Inc) : Fin 6 → ℝ := scalarShear (q.1.2, q.2)

lemma measurable_sourceCoordinates : Measurable sourceCoordinates :=
  scalarShear.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

def componentIncidence (copy : ℕ) (q : (Fin 5 → ℝ) × ℝ) : Inc := ((copy, q.1), q.2)

lemma measurable_componentIncidence (copy : ℕ) : Measurable (componentIncidence copy) := by
  exact (measurable_const.prodMk measurable_fst).prodMk measurable_snd

/-- The support of one prior component after selecting incidences and shearing. -/
def sourceComponent (copy : ℕ) (B : Set (Fin 5 → ℝ)) (C : Set Inc) : Set (Fin 6 → ℝ) :=
  {w | (scalarShear.symm w).1 ∈ B ∧ ((copy, (scalarShear.symm w).1),
    (scalarShear.symm w).2) ∈ C}

lemma sourceComponent_measurable (copy : ℕ) {B : Set (Fin 5 → ℝ)} {C : Set Inc}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    MeasurableSet (sourceComponent copy B C) := by
  exact (hB.preimage (measurable_fst.comp scalarShear.symm.measurable)).inter
    (hC.preimage ((measurable_componentIncidence copy).comp scalarShear.symm.measurable))

/-- Any volume-preserving coefficient/time coordinates give an exact selected
component law. The discrete prior copy is retained through the selection. -/
theorem component_law_in_coordinates
    (e : (Fin 5 → ℝ) × ℝ ≃ᵐ (Fin 6 → ℝ))
    (he : MeasurePreserving e ((volume : Measure (Fin 5 → ℝ)).prod volume) volume)
    (copy : ℕ) {B : Set (Fin 5 → ℝ)} {C : Set Inc}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (((Measure.map (fun a : Fin 5 → ℝ => (copy, a)) (volume.restrict B)).prod
      (volume : Measure ℝ)).restrict C).map (fun q => e (q.1.2, q.2)) =
        (volume : Measure (Fin 6 → ℝ)).restrict
          {w | (e.symm w).1 ∈ B ∧ ((copy, (e.symm w).1), (e.symm w).2) ∈ C} := by
  have hF : Measurable (fun q : Inc => e (q.1.2, q.2)) :=
    e.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet
      {w | (e.symm w).1 ∈ B ∧ ((copy, (e.symm w).1), (e.symm w).2) ∈ C} :=
    (hB.preimage (measurable_fst.comp e.symm.measurable)).inter
      (hC.preimage ((measurable_componentIncidence copy).comp e.symm.measurable))
  have hlift := measurable_componentIncidence copy
  have hprod : (Measure.map (fun a : Fin 5 → ℝ => (copy, a)) (volume.restrict B)).prod
      (volume : Measure ℝ) =
      Measure.map (componentIncidence copy)
        (((volume : Measure (Fin 5 → ℝ)).prod volume).restrict (B ×ˢ univ)) := by
    have hh := Measure.map_prod_map (volume.restrict B) (volume : Measure ℝ)
      (show Measurable (fun a : Fin 5 → ℝ => (copy, a)) from
        measurable_const.prodMk measurable_id) measurable_id
    rw [Measure.map_id] at hh
    rw [Measure.restrict_prod_eq_prod_univ] at hh
    exact hh
  rw [hprod, Measure.restrict_map hlift hC,
    Measure.map_map hF hlift]
  change Measure.map e
    ((((volume : Measure (Fin 5 → ℝ)).prod volume).restrict (B ×ˢ univ)).restrict
      (componentIncidence copy ⁻¹' C)) = _
  rw [Measure.restrict_restrict (hC.preimage hlift)]
  have hpre : e ⁻¹' {w | (e.symm w).1 ∈ B ∧ ((copy, (e.symm w).1), (e.symm w).2) ∈ C} =
      (componentIncidence copy ⁻¹' C) ∩ (B ×ˢ univ) := by
    ext q
    simp only [mem_preimage, mem_ofPred_eq,
      MeasurableEquiv.symm_apply_apply, mem_inter_iff, mem_prod, mem_univ, and_true,
      componentIncidence]
    exact and_comm
  rw [← hpre, ← Measure.restrict_map e.measurable hS, he.map_eq]

/-- Each scalar prior component has an exact selected-law density in sheared
coordinates; no regularity of a dominated residual law is used. -/
theorem scalar_component_law (copy : ℕ) {B : Set (Fin 5 → ℝ)} {C : Set Inc}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (((Measure.map (fun a : Fin 5 → ℝ => (copy, a)) (volume.restrict B)).prod
      (volume : Measure ℝ)).restrict C).map sourceCoordinates =
        (volume : Measure (Fin 6 → ℝ)).restrict (sourceComponent copy B C) := by
  exact component_law_in_coordinates scalarShear measurePreserving_scalarShear copy hB hC

/-- Component supports have twice the input degree after the inverse shear. -/
lemma sourceComponent_format (copy : ℕ) {B : Set (Fin 5 → ℝ)} {C : Set Inc}
    {HB HC : ℝ} {DB DC : ℕ} (hHB : 1 ≤ HB) (hHC : 1 ≤ HC)
    (hB : Format 5 HB DB B)
    (hC : ∀ z, Format 6 HC DC
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C}) :
    Format 6 (HB + HC) (max (DB * 2) (DC * 2)) (sourceComponent copy B C) := by
  exact k4_scalar_true_atlas_terminal_lists.Format.inter
    (prior_shear_format hHB hB) (incidence_shear_format hHC hC copy) hHB hHC

end

end Submission.Obl.k4_scalar_candidate_original_return
