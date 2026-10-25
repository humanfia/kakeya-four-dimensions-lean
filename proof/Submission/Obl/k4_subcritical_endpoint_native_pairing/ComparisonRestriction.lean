/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/ComparisonRestriction.lean.
   Original source attributions are retained below. -/
import Mathlib

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory

/-- Summing the matching failures over disjoint read domains gives one good
restriction. The domain reference weights remain those of the pre-deletion law. -/
theorem restrict_comparison_failures {Ω Γ : Type*} [MeasurableSpace Ω]
    [Fintype Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (μ : Measure Ω) (reader : Ω → Γ) (hreader : Measurable reader)
    (bad : Γ → Set Ω) (hbad : ∀ g, MeasurableSet (bad g))
    (reference : Γ → ENNReal) (C B : ENNReal)
    (hfailure : ∀ g, (μ.restrict (reader ⁻¹' {g})) (bad g) ≤ C * reference g)
    (hbudget : (∑ g, reference g) ≤ B) :
    ∃ ρ : Measure Ω, ρ ≤ μ ∧ μ univ ≤ ρ univ + C * B ∧
      ∀ᵐ p ∂ρ, p ∉ bad (reader p) := by
  let U : Set Ω := ⋃ g, bad g ∩ reader ⁻¹' {g}
  have hU : MeasurableSet U :=
    MeasurableSet.iUnion fun g => (hbad g).inter (hreader (measurableSet_singleton g))
  have hloss : μ U ≤ C * B := by
    calc
      _ ≤ ∑ g, μ (bad g ∩ reader ⁻¹' {g}) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ g, C * reference g := by
        apply Finset.sum_le_sum
        intro g hg
        rw [← Measure.restrict_apply (hbad g)]
        exact hfailure g
      _ = C * ∑ g, reference g := (Finset.mul_sum _ _ _).symm
      _ ≤ C * B := mul_le_mul' le_rfl hbudget
  refine ⟨μ.restrict Uᶜ, Measure.restrict_le_self, ?_, ?_⟩
  · rw [Measure.restrict_apply_univ]
    calc
      μ univ = μ Uᶜ + μ U := by
        simpa only [compl_compl] using (measure_add_measure_compl hU.compl).symm
      _ ≤ _ := add_le_add le_rfl hloss
  · filter_upwards [ae_restrict_mem hU.compl] with p hp
    intro h
    exact hp (mem_iUnion.mpr ⟨reader p, h, by simp⟩)

end Submission.Obl.k4_subcritical_endpoint_native_pairing
