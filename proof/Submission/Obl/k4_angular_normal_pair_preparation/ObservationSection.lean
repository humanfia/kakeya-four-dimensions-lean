-- Adapted from this LOT tree, o206, session x0709, commit f7d6ac58, ObservationSection.lean.
import Submission.Obl.k4_angular_normal_pair_preparation.Definitions

/-! Measurability of old lists in the observation space from the frozen hypothesis. -/

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory Set

/-- A canonical incidence realizing an arbitrary observed spacetime point and
hidden bin. The trajectory has zero velocity and label zero. -/
noncomputable def observationSection (B a : ℝ) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    (ℕ × (Fin 6 → ℝ)) × ℝ :=
  ((0, ![o.1 1, o.1 2, (o.2 : ℝ) * a / B, 0, 0, 0]), o.1 0)

theorem continuous_observationSection (B a : ℝ) : Continuous (observationSection B a) := by
  unfold observationSection
  refine (continuous_const.prodMk ?_).prodMk (by fun_prop)
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem observationSection_rightInverse {B a : ℝ} (hB : B ≠ 0) (ha : a ≠ 0)
    (o : EuclideanSpace ℝ (Fin 3) × ℤ) : obs B a (observationSection B a o) = o := by
  rcases o with ⟨z, n⟩
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [obs, Submission.Obl.k4_extremal_profile_setup.obs, observationSection, x, Submission.Obl.k4_extremal_profile_setup.x]
  · have heq : B * ((n : ℝ) * a / B) / a = (n : ℝ) := by field_simp
    simp [obs, Submission.Obl.k4_extremal_profile_setup.obs, observationSection, x, Submission.Obl.k4_extremal_profile_setup.x, heq]

/-- Pullback measurability along the frozen observation implies measurability
of the observed set itself. No Boolean-format assumption is needed for this step. -/
theorem measurableSet_of_observation_preimage {B a : ℝ} (hB : B ≠ 0) (ha : a ≠ 0)
    {S : Set (EuclideanSpace ℝ (Fin 3) × ℤ)}
    (hS : MeasurableSet ((obs B a) ⁻¹' S)) : MeasurableSet S := by
  have h := hS.preimage (continuous_observationSection B a).measurable
  convert h using 1
  ext o
  simp only [mem_preimage, observationSection_rightInverse hB ha]

/-- The old-list measurability used by angular integration follows from the
exact incidence-pullback measurability in `known`. -/
theorem measurableSet_list_of_incidence_membership {ι : Type*} {B a : ℝ}
    (hB : B ≠ 0) (ha : a ≠ 0) (lst : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset ι)
    (hlst : ∀ i, MeasurableSet {p | i ∈ lst (obs B a p)}) :
    ∀ i, MeasurableSet {o | i ∈ lst o} := by
  intro i
  exact measurableSet_of_observation_preimage hB ha (hlst i)

end Submission.Obl.k4_angular_normal_pair_preparation
