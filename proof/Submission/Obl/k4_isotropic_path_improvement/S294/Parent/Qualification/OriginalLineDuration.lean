-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalLineDuration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.UnitIncidenceKernel

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open Submission.Lib.K4Homogenization
open scoped ENNReal

noncomputable section

/-- Cut whole original lines with short occupation. Both the duration and
the deletion are measured with the unchanged original product law. -/
theorem exists_original_line_duration_source {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (A : Set Λ) (hA : MeasurableSet A) (hEA : E ⊆ A ×ˢ univ)
    (duration : ENNReal) :
    ∃ S : Set Λ, MeasurableSet S ∧ S⊆A ∧
      (ν.prod volume) (E\(E∩(S×ˢ univ))) ≤ duration*ν univ ∧
      ∀ l∈S, duration ≤ volume {t | (l,t)∈E∩(S×ˢ univ)} := by
  let G := originalUnitEventDensity E
  have hG : Measurable G := originalUnitEventDensity_measurable hE
  let Long := durationRetained (volume : Measure ℝ) G univ duration
  have hLong : MeasurableSet Long := measurableSet_durationRetained volume hG univ duration
  let S := A∩Long
  have hS : MeasurableSet S := hA.inter hLong
  have hDensity : (ν.prod volume).withDensity G = (ν.prod volume).restrict E := by
    dsimp only [G,originalUnitEventDensity]
    rw [withDensity_indicator hE,withDensity_const,one_smul]
  refine ⟨S,hS,inter_subset_left,?_,?_⟩
  · have h := duration_omission_mass_le ν volume hG MeasurableSet.univ duration
    rw [hDensity,Measure.restrict_apply (hLong.compl.prod MeasurableSet.univ)] at h
    apply (measure_mono ?_).trans h
    intro z hz
    refine ⟨⟨?_,mem_univ _⟩,hz.1⟩
    intro hl
    exact hz.2 ⟨hz.1,⟨(hEA hz.1).1,hl⟩,mem_univ _⟩
  · intro l hl
    have h := hl.2
    change duration ≤ ∫⁻ t in univ, G (l,t) at h
    have hf : (fun t : ℝ => G (l,t)) = {t | (l,t)∈E}.indicator (fun _ => (1:ENNReal)) := rfl
    have hmeas : MeasurableSet {t | (l,t)∈E} :=
      hE.preimage (measurable_const.prodMk measurable_id)
    have htimes : {t | (l,t)∈E∩(S×ˢ univ)} = {t | (l,t)∈E} := by
      ext t
      simp only [mem_ofPred_eq,mem_inter_iff,mem_prod,mem_univ,and_true,hl]
    rw [hf,setLIntegral_univ,lintegral_indicator hmeas,lintegral_one] at h
    simpa only [htimes,Measure.restrict_apply_univ] using h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
