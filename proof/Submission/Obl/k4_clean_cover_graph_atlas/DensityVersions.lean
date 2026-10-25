-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/DensityVersions.lean (namespace renamed).

import Mathlib

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory

/-- Finite absolutely continuous observation laws have nonnegative measurable real
integrable density versions, suitable for exact finite posterior pairing. -/
theorem exists_real_density {X : Type*} [MeasurableSpace X]
    (μ ρ : Measure X) [IsFiniteMeasure μ] [SigmaFinite ρ] (hμ : μ ≪ ρ) :
    ∃ p : X → ℝ, Measurable p ∧ Integrable p ρ ∧ (∀ x, 0 ≤ p x) ∧
      ρ.withDensity (fun x => ENNReal.ofReal (p x)) = μ := by
  let p : X → ℝ := fun x => (μ.rnDeriv ρ x).toReal
  refine ⟨p, (Measure.measurable_rnDeriv μ ρ).ennreal_toReal,
    Measure.integrable_toReal_rnDeriv, fun _ => ENNReal.toReal_nonneg, ?_⟩
  calc
    _ = ρ.withDensity (μ.rnDeriv ρ) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top μ ρ] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    _ = μ := Measure.withDensity_rnDeriv_eq μ ρ hμ

/-- Density versions can retain a specified measurable geometric support everywhere,
so positive posterior entries carry their original fitting certificate. -/
theorem exists_real_density_supported {X : Type*} [MeasurableSpace X]
    (μ ρ : Measure X) [IsFiniteMeasure μ] [SigmaFinite ρ] (hμ : μ ≪ ρ)
    (S : Set X) (hS : MeasurableSet S) (hsupport : μ Sᶜ = 0) :
    ∃ p : X → ℝ, Measurable p ∧ Integrable p ρ ∧ (∀ x, 0 ≤ p x) ∧
      ρ.withDensity (fun x => ENNReal.ofReal (p x)) = μ ∧
      ∀ x, 0 < p x → x ∈ S := by
  classical
  obtain ⟨p, hpmeas, hpint, hp, hlaw⟩ := exists_real_density μ ρ hμ
  have hrestrict : μ.restrict S = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact hsupport
  refine ⟨S.indicator p, hpmeas.indicator hS, hpint.indicator hS, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ S <;> simp [hx, hp]
  · have heq : (fun x => ENNReal.ofReal (S.indicator p x)) =
        S.indicator (fun x => ENNReal.ofReal (p x)) := by
      funext x
      by_cases hx : x ∈ S <;> simp [hx]
    rw [heq, withDensity_indicator hS, ← restrict_withDensity hS, hlaw, hrestrict]
  · intro x hx
    by_contra hn
    simpa [hn] using hx

end Submission.Obl.k4_clean_cover_graph_atlas
