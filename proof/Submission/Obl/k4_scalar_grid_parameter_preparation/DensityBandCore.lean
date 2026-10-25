/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/DensityBandCore.lean -/
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.RawCeiling
import Submission.Lib.K4ModelReduction.DensityOperations

/-! A density band can be imposed after the common trace mask, with an explicit loss. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped ENNReal

/-- Remove low original density inside a set of reference mass at most one.  The resulting
law is compared with the original reference measure on the very same retained set. -/
theorem exists_density_band_core {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω) [SigmaFinite μ] (U a : ℝ≥0∞)
    (hU : U ≠ ⊤) (hdom : ρ ≤ U • μ)
    (S E₀ : Set Ω) (hS : MeasurableSet S) (hS₁ : μ S ≤ 1)
    (hE₀ : MeasurableSet E₀) (hsub : E₀ ⊆ S) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ E₀ ∧ ρ (E₀ \ E) ≤ a ∧
      a • μ.restrict E ≤ ρ.restrict E ∧ ρ.restrict E ≤ U • μ.restrict E := by
  let G := ρ.rnDeriv μ
  obtain ⟨hG, hρ, hGupper⟩ :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw.exists_density_le hU hdom
  change Measurable G at hG
  change ρ = μ.withDensity G at hρ
  change ∀ᵐ x ∂μ, G x ≤ U at hGupper
  let E := E₀ ∩ {x | a ≤ G x ∧ G x ≤ U}
  have hE : MeasurableSet E := hE₀.inter
    ((measurableSet_le measurable_const hG).inter (measurableSet_le hG measurable_const))
  have hGE : ∀ᵐ x ∂μ.restrict E, a ≤ G x ∧ G x ≤ U :=
    (ae_restrict_mem hE).mono fun x hx => hx.2
  have hGρ : ∀ᵐ x ∂ρ, G x ≤ U :=
    ae_mono hdom (Measure.ae_smul_measure hGupper U)
  have hhigh : ρ {x | U < G x} = 0 := by
    simpa only [not_le] using (ae_iff.mp hGρ)
  let indicator : Ω → ℝ≥0∞ := S.indicator (fun _ => 1)
  have hind : Measurable indicator := measurable_const.indicator hS
  have hlow : ρ (E₀ ∩ {x | G x < a}) ≤ a := by
    calc
      _ ≤ ρ {x | G x < a * indicator x} := by
        apply measure_mono
        intro x hx
        change G x < a * indicator x
        simpa only [indicator, Set.indicator_of_mem (hsub hx.1), mul_one] using
          (show G x < a from hx.2)
      _ ≤ a * ∫⁻ x, indicator x ∂μ := by
        rw [hρ]
        exact Submission.Lib.K4ModelReduction.lower_density_ratio_mass_bound
          μ G indicator hG hind a
      _ = a * μ S := by simp [indicator, lintegral_indicator hS]
      _ ≤ a * 1 := mul_le_mul le_rfl hS₁ bot_le bot_le
      _ = a := mul_one _
  have hloss : ρ (E₀ \ E) ≤ a := by
    calc
      _ ≤ ρ ((E₀ ∩ {x | G x < a}) ∪ {x | U < G x}) := by
        apply measure_mono
        intro x hx
        by_cases hlow : a ≤ G x
        · exact Or.inr (lt_of_not_ge fun hhigh => hx.2 ⟨hx.1, hlow, hhigh⟩)
        · exact Or.inl ⟨hx.1, lt_of_not_ge hlow⟩
      _ ≤ ρ (E₀ ∩ {x | G x < a}) + ρ {x | U < G x} := measure_union_le _ _
      _ ≤ a := by simpa only [hhigh, add_zero] using hlow
  refine ⟨E, hE, inter_subset_left, hloss, ?_, ?_⟩
  · rw [hρ, restrict_withDensity hE, ← withDensity_const]
    exact withDensity_mono (hGE.mono fun x hx => hx.1)
  · rw [hρ, restrict_withDensity hE, ← withDensity_const]
    exact withDensity_mono (hGE.mono fun x hx => hx.2)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
