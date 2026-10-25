/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, DensityRestriction.lean.
   Original source attributions below are retained. -/

import Submission.Lib.K4ModelReduction.DensityOperations

/-! Adapted from our LOT tree o107 (`k4_finite_narrowness_path_improvement`), session x0353,
`DensityRestriction.lean` (commit 96bcaa7b); namespace and import paths renamed. -/

/-! Density level sets compare continuous original incidence laws with
restrictions of the same reference measure. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set
open scoped ENNReal

/-- An original density may be bounded below on a measurable restriction at
the cost of the cutoff times the original reference mass. -/
theorem density_level_restriction
    {Ω : Type*} [MeasurableSpace Ω] (m μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) (hlaw : μ = m.withDensity f)
    (U : Set Ω) (hU : MeasurableSet U) (cutoff : ℝ≥0∞) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ U ∧
      (∀ x ∈ E, cutoff ≤ f x) ∧ cutoff • m.restrict E ≤ μ.restrict U ∧
      μ (U \ E) ≤ cutoff * m U := by
  let E := U ∩ {x | cutoff ≤ f x}
  have hE : MeasurableSet E := hU.inter (measurableSet_le measurable_const hf)
  have hEU : E ⊆ U := Set.inter_subset_left
  refine ⟨E, hE, hEU, (fun x hx => hx.2), ?_, ?_⟩
  · calc
      _ = (m.restrict E).withDensity (fun _ => cutoff) := (withDensity_const _).symm
      _ ≤ (m.restrict E).withDensity f := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem hE] with x hx
        exact hx.2
      _ = (m.withDensity f).restrict E := (restrict_withDensity hE f).symm
      _ ≤ (m.withDensity f).restrict U := Measure.restrict_mono_set _ hEU
      _ = _ := by rw [hlaw]
  · have hlow := Submission.Lib.K4ModelReduction.lower_density_ratio_mass_bound
      (m.restrict U) f (fun _ => 1) hf measurable_const cutoff
    have hdiff : U \ E = {x | f x < cutoff} ∩ U := by
      ext x
      simp only [E, mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_and, not_le]
      tauto
    rw [hdiff, hlaw, ← Measure.restrict_apply (measurableSet_lt hf measurable_const),
      restrict_withDensity hU]
    simpa only [mul_one, lintegral_const, one_mul, Measure.restrict_apply_univ] using hlow

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
