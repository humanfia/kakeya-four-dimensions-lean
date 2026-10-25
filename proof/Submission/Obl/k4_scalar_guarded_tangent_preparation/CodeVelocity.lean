import Submission.Obl.k4_row_cell_regularization.Palette

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

def velocityValues {n : ℕ} (Z : Fin n → ℤ) : Finset ℤ :=
  Finset.univ.image Z

def finiteVelocityCode {Ω : Type*} {n : ℕ} (X : Ω → Fin n) (Z : Fin n → ℤ)
    (x : Ω) : velocityValues Z :=
  ⟨Z (X x), Finset.mem_image.mpr ⟨X x, Finset.mem_univ _, rfl⟩⟩

theorem measurable_finiteVelocityCode
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Ω → Fin n) (hX : Measurable X) (Z : Fin n → ℤ) :
    Measurable (finiteVelocityCode X Z) :=
  ((measurable_of_finite Z).comp hX).subtype_mk

theorem finiteVelocityCode_fiber {Ω : Type*} {n : ℕ}
    (X : Ω → Fin n) (Z : Fin n → ℤ) (i : velocityValues Z) :
    (finiteVelocityCode X Z ⁻¹' {i}) = {x | Z (X x) = i.val} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff,
    finiteVelocityCode, Set.mem_ofPred_eq]

/-- A floor-bin's left endpoint is a valid fine velocity center. -/
theorem floor_center_error {δ v : ℝ} (hδ : 0 < δ) (e : ℤ)
    (he : (⌊v / δ⌋ : ℤ) = e) : |v - (e : ℝ) * δ| ≤ δ := by
  have hv : v ∈ Ico ((e : ℝ) * δ) (((e : ℝ) + 1) * δ) := by
    change v ∈ Submission.Obl.k4_row_cell_regularization.velocityCell δ e
    rw [Submission.Obl.k4_row_cell_regularization.velocityCell_eq_floor hδ]
    exact he
  apply abs_le.mpr
  constructor <;> nlinarith [hv.1, hv.2]

/-- The pre-mask probabilities of distinct velocity codes sum to one.
The same weights define the fixed blurred palette. -/
theorem finite_code_probabilities
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ι) (hU : Measurable U) :
    (∀ i, 0 ≤ μ.real (U ⁻¹' {i})) ∧
    (∑ i, μ.real (U ⁻¹' {i})) = 1 ∧
    ∀ i, ENNReal.ofReal (μ.real (U ⁻¹' {i})) = μ (U ⁻¹' {i}) := by
  classical
  refine ⟨fun _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · simpa using (sum_measureReal_preimage_singleton Finset.univ
      (μ := μ) (fun i _ => hU (measurableSet_singleton i)))
  · intro i
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- Normalization is used only for reference probabilities. This identity
keeps the original total mass in every later likelihood denominator. -/
theorem original_cond_mass_identity
    {Ω : Type*} [MeasurableSpace Ω] (σ : Measure Ω) [IsFiniteMeasure σ] (E : Set Ω) :
    σ.real E = σ.real univ * (ProbabilityTheory.cond σ univ).real E := by
  have h := ProbabilityTheory.cond_mul_eq_inter' (μ := σ) MeasurableSet.univ
    (measure_ne_top σ univ) E
  have hr := congrArg ENNReal.toReal h
  simpa only [univ_inter, ENNReal.toReal_mul, measureReal_def, mul_comm] using hr.symm

/-- An original marginal identity is preserved when only its total mass
is normalized to a reference probability. -/
theorem cond_map_of_original_marginal
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (σ : Measure Ω) [IsFiniteMeasure σ] (hm : σ univ ≠ 0)
    (V : Ω → Λ) (hV : Measurable V) (π : Measure Λ) (hlaw : σ.map V = (σ univ) • π) :
    (ProbabilityTheory.cond σ univ).map V = π := by
  rw [ProbabilityTheory.cond, Measure.restrict_univ, Measure.map_smul, hlaw,
    smul_smul, ENNReal.inv_mul_cancel hm (measure_ne_top σ univ), one_smul]
  exact hV.aemeasurable

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
