-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.DyadicVelocityReference, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SnapshotDyadicScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- One original finest-bin palette, placed at the literal bin corners.
It is fixed before all coarser queries. -/
def dyadicVelocityReference {m : ℕ} (finest : ℕ) (π : Measure (Fin m → ℤ)) :
    Measure (Fin m → ℝ) :=
  π.map (fun b => fun i => dyadicParameterWidth finest*(b i:ℝ))

theorem dyadicVelocityReference_probability {m : ℕ} (finest : ℕ)
    (π : Measure (Fin m → ℤ)) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (dyadicVelocityReference finest π) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr inferInstance

theorem parameterCode_dyadic_corner {m : ℕ} {query finest : ℕ} (hle : query ≤ finest)
    (b : Fin m → ℤ) :
    parameterCode (dyadicParameterWidth query)
      (fun i => dyadicParameterWidth finest*(b i:ℝ))=coarsenParameterCode (finest-query) b := by
  have hfinest : parameterCode (dyadicParameterWidth finest)
      (fun i => dyadicParameterWidth finest*(b i:ℝ))=b := by
    funext i
    change ⌊(dyadicParameterWidth finest*(b i:ℝ))/dyadicParameterWidth finest⌋=b i
    rw [mul_div_cancel_left₀ _ (dyadicParameterWidth_pos _).ne',Int.floor_intCast]
  have h := coarsen_nested_parameterCode 1 (by norm_num) hle
    (fun i => dyadicParameterWidth finest*(b i:ℝ))
  simpa only [one_mul,hfinest] using h.symm

/-- Every queried velocity-bin law is the literal pushforward of the
same original finest palette. There is no separate normalization by query. -/
theorem dyadicVelocityReference_map_code {m : ℕ} (π : Measure (Fin m → ℤ))
    {query finest : ℕ} (hle : query ≤ finest) :
    (dyadicVelocityReference finest π).map (parameterCode (dyadicParameterWidth query))=
      π.map (coarsenParameterCode (finest-query)) := by
  unfold dyadicVelocityReference
  rw [Measure.map_map (measurable_parameterCode _) (measurable_of_countable _)]
  congr 1
  funext b
  exact parameterCode_dyadic_corner hle b

theorem dyadicVelocityReference_code_event {m : ℕ} (π : Measure (Fin m → ℤ))
    {query finest : ℕ} (hle : query ≤ finest) (D : Set (Fin m → ℤ)) :
    (dyadicVelocityReference finest π) {v | parameterCode (dyadicParameterWidth query) v∈D}=
      π {b | coarsenParameterCode (finest-query) b∈D} := by
  have hD : MeasurableSet D := (Set.to_countable D).measurableSet
  change (dyadicVelocityReference finest π) ((parameterCode (dyadicParameterWidth query)) ⁻¹' D)=
    π ((coarsenParameterCode (finest-query)) ⁻¹' D)
  rw [←Measure.map_apply (measurable_parameterCode _) hD,dyadicVelocityReference_map_code π hle,
    Measure.map_apply (measurable_of_countable _) hD]

/-- All-D original finest-bin incidence caps yield every coarser
velocity-bin event cap against ONE fixed real-valued reference. The
incidence measure, its original source and the external factor are unchanged. -/
theorem original_velocity_caps_under_dyadic_reference {Ω : Type*} [MeasurableSpace Ω]
    {m : ℕ} (μ : Measure Ω) (A : Set Ω) (velocity : Ω → Fin m → ℝ)
    (finest : ℕ) (π : Measure (Fin m → ℤ)) (C : ENNReal)
    (hcap : ∀ D : Set (Fin m → ℤ), MeasurableSet D →
      μ {z | z∈A ∧ parameterCode (dyadicParameterWidth finest) (velocity z)∈D} ≤ C*π D) :
    ∀ query : ℕ, query ≤ finest → ∀ D : Set (Fin m → ℤ),
      μ {z | z∈A ∧ parameterCode (dyadicParameterWidth query) (velocity z)∈D} ≤
        C*(dyadicVelocityReference finest π) {v | parameterCode (dyadicParameterWidth query) v∈D} := by
  intro query hle D
  rw [dyadicVelocityReference_code_event π hle D]
  have hvelocity (z : Ω) :
      coarsenParameterCode (finest-query) (parameterCode (dyadicParameterWidth finest) (velocity z))=
        parameterCode (dyadicParameterWidth query) (velocity z) := by
    simpa only [one_mul] using coarsen_nested_parameterCode 1 (by norm_num) hle (velocity z)
  have h := hcap ((coarsenParameterCode (finest-query)) ⁻¹' D)
    ((Set.to_countable _).measurableSet)
  simpa only [Set.preimage,mem_ofPred_eq,hvelocity] using h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
