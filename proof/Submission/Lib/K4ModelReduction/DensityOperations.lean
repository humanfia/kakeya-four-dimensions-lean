import Mathlib

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-!
Restriction and omitted-mass comparisons in the supplied paper's Lemma
`a01:density-operations`, in exact finite-tolerance form.
-/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- A restricted density can fall below a fixed fraction of the original
density on at most that fraction of the original mass. -/
theorem lower_density_ratio_mass_bound (μ : Measure X) (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (ε : ℝ≥0∞) :
    μ.withDensity f {x | f x < ε * g x} ≤ ε * ∫⁻ x, g x ∂μ := by
  have hset : MeasurableSet {x | f x < ε * g x} :=
    measurableSet_lt hf (measurable_const.mul hg)
  rw [withDensity_apply _ hset]
  calc
    ∫⁻ x in {x | f x < ε * g x}, f x ∂μ ≤
        ∫⁻ x in {x | f x < ε * g x}, ε * g x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hset] with x hx
      exact hx.le
    _ = ε * ∫⁻ x in {x | f x < ε * g x}, g x ∂μ := lintegral_const_mul _ hg
    _ ≤ ε * ∫⁻ x, g x ∂μ :=
      mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _

/-- Exact finite-tolerance form of preservation of typical densities under
further restriction. The new lower threshold is the old one times `ε`. -/
theorem restricted_density_exception_bound (μ : Measure X) (f g : X → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∀ x, f x ≤ g x)
    (ε lower upper : ℝ≥0∞) :
    μ.withDensity f {x | f x < ε * lower ∨ upper < f x} ≤
      μ.withDensity g {x | g x < lower ∨ upper < g x} + ε * ∫⁻ x, g x ∂μ := by
  have hsub : {x | f x < ε * lower ∨ upper < f x} ⊆
      {x | g x < lower ∨ upper < g x} ∪ {x | f x < ε * g x} := by
    intro x hx
    by_cases hbad : g x < lower ∨ upper < g x
    · exact Or.inl hbad
    · apply Or.inr
      have hlower : lower ≤ g x := le_of_not_gt (fun h => hbad (Or.inl h))
      rcases hx with hlow | hhigh
      · exact hlow.trans_le (mul_le_mul_right hlower ε)
      · exact (hbad (Or.inr (hhigh.trans_le (hfg x)))).elim
  have hdom : μ.withDensity f ≤ μ.withDensity g :=
    withDensity_mono (Filter.Eventually.of_forall hfg)
  calc
    _ ≤ μ.withDensity f ({x | g x < lower ∨ upper < g x} ∪ {x | f x < ε * g x}) :=
      measure_mono hsub
    _ ≤ μ.withDensity f {x | g x < lower ∨ upper < g x} +
        μ.withDensity f {x | f x < ε * g x} := measure_union_le _ _
    _ ≤ _ := add_le_add (hdom _) (lower_density_ratio_mass_bound μ f g hf hg ε)

/-- If an omitted density dominates the retained density at an observation,
the full mass of those observations is at most twice the omitted mass. -/
theorem omitted_density_dominates_mass_bound (μ : Measure X) (good bad : X → ℝ≥0∞)
    (hgood : Measurable good) (hbad : Measurable bad) :
    μ.withDensity (fun x => good x + bad x) {x | good x < bad x} ≤
      2 * ∫⁻ x, bad x ∂μ := by
  have hset : MeasurableSet {x | good x < bad x} := measurableSet_lt hgood hbad
  rw [withDensity_apply _ hset]
  calc
    ∫⁻ x in {x | good x < bad x}, good x + bad x ∂μ ≤
        ∫⁻ x in {x | good x < bad x}, 2 * bad x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hset] with x hx
      simpa only [two_mul] using add_le_add hx.le le_rfl
    _ = 2 * ∫⁻ x in {x | good x < bad x}, bad x ∂μ := lintegral_const_mul _ hbad
    _ ≤ 2 * ∫⁻ x, bad x ∂μ :=
      mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _

end Submission.Lib.K4ModelReduction
