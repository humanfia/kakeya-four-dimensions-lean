-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CommonDyadicVelocityReference, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicVelocityReference
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ProbabilityPaletteExtension
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CurrentVelocitySpatialCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.VelocityPaletteCoarsening

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- One real reference dominates the four compatible bins of the fixed
original fine palette at one dyadic cutoff. All further coarsenings use
this same reference. -/
structure CommonDyadicVelocityReference (fineWidth : ℝ) (finest : ℕ)
    (weight : (Fin 2 → ℤ) → ENNReal) (π : Measure (Fin 2 → ℝ)) : Prop where
  probability : IsProbabilityMeasure π
  code_floor : ∀ b,
    ParentSource.Broad.Source.Jets2.velocityPaletteAt fineWidth (dyadicParameterWidth finest) weight b ≤
      π {v | parameterCode (dyadicParameterWidth finest) v=b}

/-- A possibly nonaligned original finest-bin palette constructs ONE
probability reference. The construction precedes every incidence law,
state, cell and coarser query to which it will be applied. -/
theorem exists_common_dyadic_velocity_reference (fineWidth : ℝ) (finest : ℕ)
    (weight : (Fin 2 → ℤ) → ENNReal) (hweight : (∑' b, weight b) ≤ 1) :
    ∃ π : Measure (Fin 2 → ℝ), CommonDyadicVelocityReference fineWidth finest weight π := by
  let weights := ParentSource.Broad.Source.Jets2.velocityPaletteAt
    fineWidth (dyadicParameterWidth finest) weight
  have hweights : (∑' b, weights b) ≤ 1 :=
    ParentSource.Broad.Source.Jets2.tsum_velocityPaletteAt_le_one _ _ _ hweight
  obtain ⟨discrete,hprob,_hdom,hpoint⟩ := exists_probability_palette_dominating_weights
    (0 : Fin 2 → ℤ) weights hweights
  letI := hprob
  refine ⟨dyadicVelocityReference finest discrete,
    dyadicVelocityReference_probability finest discrete,?_⟩
  intro b
  have hzero (a : Fin 2 → ℤ) : coarsenParameterCode 0 a=a := by
    funext j
    simp only [coarsenParameterCode,pow_zero,Int.ediv_one]
  have h := dyadicVelocityReference_code_event discrete (le_refl finest) {b}
  simp only [Nat.sub_self,hzero,mem_singleton_iff] at h
  rw [h]
  exact hpoint b

/-- The original fine-bin caps transfer to every coarser dyadic test
against the SAME real probability reference at cost four. The source,
state references and original incidence measure are untouched. -/
theorem CommonDyadicVelocityReference.current_caps
    {fineWidth : ℝ} {finest : ℕ} {weight : (Fin 2 → ℤ) → ENNReal}
    {π : Measure (Fin 2 → ℝ)} (reference : CommonDyadicVelocityReference fineWidth finest weight π)
    (hfine : 0 < fineWidth) (hwidth : fineWidth ≤ dyadicParameterWidth finest)
    {Ω Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (velocity : Ω → Fin 2 → ℝ) (hvelocity : Measurable velocity)
    (mass : Q → ENNReal) (C : ENNReal)
    (hcap : ∀ q b, μ {z | state z=q ∧ parameterCode fineWidth (velocity z)=b} ≤
      C*mass q*weight b) :
    ∀ query : ℕ, query ≤ finest → ∀ q (D : Set (Fin 2 → ℤ)),
      μ {z | state z=q ∧ parameterCode (dyadicParameterWidth query) (velocity z)∈D} ≤
        (4*C)*mass q*π {v | parameterCode (dyadicParameterWidth query) v∈D} := by
  intro query hquery q D
  classical
  let A := state ⁻¹' {q}
  have hA : MeasurableSet A := hstate (measurableSet_singleton q)
  have hcutoff (b : Fin 2 → ℤ) :
      μ {z | state z=q ∧ parameterCode (dyadicParameterWidth finest) (velocity z)=b} ≤
        (4*C)*mass q*π {v | parameterCode (dyadicParameterWidth finest) v=b} :=
    (ParentSource.Broad.Source.Jets2.velocityPaletteAt_state_cap μ state hstate velocity hvelocity
      hfine hwidth weight mass C hcap q b).trans
        (mul_le_mul' le_rfl (reference.code_floor b))
  let code := fun z : Ω => parameterCode (dyadicParameterWidth finest) (velocity z)
  have hcode : Measurable code := (measurable_parameterCode _).comp hvelocity
  have hsingle (b : Fin 2 → ℤ) :
      (μ.restrict A) (code ⁻¹' {b}) ≤
        (4*C)*mass q*π ((parameterCode (dyadicParameterWidth finest)) ⁻¹' {b}) := by
    rw [Measure.restrict_apply' hA]
    convert hcutoff b using 2
    · ext z
      simp only [A,code,mem_preimage,mem_singleton_iff,mem_inter_iff,mem_ofPred_eq,and_comm]
    · rfl
  let selector := fun b : Fin 2 → ℤ => decide (coarsenParameterCode (finest-query) b∈D)
  have h := palette_cap_of_code_coarsening (μ.restrict A) π code hcode
    (parameterCode (dyadicParameterWidth finest)) (measurable_parameterCode _) selector
    ((4*C)*mass q) hsingle true
  have hcoarsen (v : Fin 2 → ℝ) :
      coarsenParameterCode (finest-query) (parameterCode (dyadicParameterWidth finest) v)=
        parameterCode (dyadicParameterWidth query) v := by
    simpa only [one_mul] using coarsen_nested_parameterCode 1 (by norm_num) hquery v
  simp only [selector,code,decide_eq_true_eq,hcoarsen] at h
  rw [Measure.restrict_apply' hA] at h
  convert h using 2
  ext z
  simp only [A,mem_preimage,mem_singleton_iff,mem_inter_iff,mem_ofPred_eq,and_comm]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
